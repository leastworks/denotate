//! Signed SCCs of the equations, before W or H. A parity-consistent SCC is
//! monotone after complementing one colour: Tarski gives a fixed point for any
//! boundary assignment. SCC composition therefore proves totality, not uniqueness.
use super::*;

pub(super) struct Core {
    pub needed: Vec<bool>,
    pub odd_components: usize,
    pub odd_atoms: usize,
    component: Vec<usize>,
    colour: Vec<Option<bool>>,
}

pub(super) fn analyse(c: &Cone, boundary: Option<&[bool]>, b: &mut Budget<'_>) -> Result<Core> {
    let n = c.fixed.len();
    b.charge(n + c.rules.len(), "completion call consistency")?;
    let mut edges = vec![Vec::new(); n];
    let mut reverse = vec![Vec::new(); n];
    let fixed = |i: usize| c.fixed[i].or_else(|| boundary.filter(|_| c.input[i]).map(|v| v[i]));
    for r in &c.rules {
        b.charge(r.body.len() + 1, "completion call consistency")?;
        if c.input[r.head]
            || c.fixed[r.head].is_some()
            || r.body
                .iter()
                .any(|(i, p)| fixed(*i).is_some_and(|v| v != *p))
        {
            continue;
        }
        for &(i, positive) in &r.body {
            if c.input[i] || c.fixed[i].is_some() {
                continue;
            }
            edges[r.head].push((i, !positive));
            reverse[i].push(r.head);
        }
    }
    // Iterative Kosaraju avoids stack depth depending on the authored program.
    let mut seen = vec![false; n];
    let mut order = Vec::with_capacity(n);
    for root in 0..n {
        if seen[root] {
            continue;
        }
        seen[root] = true;
        let mut stack = vec![(root, 0)];
        while let Some((i, next)) = stack.last_mut() {
            b.tick("completion call consistency")?;
            if *next == edges[*i].len() {
                order.push(*i);
                stack.pop();
                continue;
            }
            let j = edges[*i][*next].0;
            *next += 1;
            if !seen[j] {
                seen[j] = true;
                stack.push((j, 0));
            }
        }
    }
    let mut component = vec![usize::MAX; n];
    let mut groups = Vec::new();
    for root in order.into_iter().rev() {
        if component[root] != usize::MAX {
            continue;
        }
        let id = groups.len();
        let mut members = Vec::new();
        let mut pending = vec![root];
        component[root] = id;
        while let Some(i) = pending.pop() {
            b.charge(reverse[i].len() + 1, "completion call consistency")?;
            members.push(i);
            for &j in &reverse[i] {
                if component[j] == usize::MAX {
                    component[j] = id;
                    pending.push(j);
                }
            }
        }
        groups.push(members);
    }
    let mut colour = vec![None; n];
    let mut pending: Vec<usize> = Vec::new();
    let mut odd_components = 0;
    let mut odd_atoms = 0;
    for (id, members) in groups.iter().enumerate() {
        let root = members[0];
        colour[root] = Some(false);
        let mut queue = vec![root];
        let mut odd = false;
        while let Some(i) = queue.pop() {
            b.charge(edges[i].len() + 1, "completion call consistency")?;
            for &(j, negative) in &edges[i] {
                if component[j] != id {
                    continue;
                }
                let expected = colour[i].unwrap() ^ negative;
                match colour[j] {
                    Some(v) => odd |= v != expected,
                    None => {
                        colour[j] = Some(expected);
                        queue.push(j);
                    }
                }
            }
        }
        if odd {
            odd_components += 1;
            odd_atoms += members.len();
            pending.extend(members.iter().copied());
        }
    }
    // Preserve all providers of an odd SCC. Everything outside this closure is
    // call-consistent and can extend any interpretation of the retained part.
    let mut needed = vec![false; n];
    while let Some(i) = pending.pop() {
        if needed[i] {
            continue;
        }
        needed[i] = true;
        b.charge(edges[i].len() + 1, "completion call consistency")?;
        pending.extend(edges[i].iter().map(|(j, _)| *j));
    }
    Ok(Core {
        needed,
        odd_components,
        odd_atoms,
        component,
        colour,
    })
}

/// Keep disabled the rules that could break the signed SCC ordering/colouring.
/// Other edges may appear or disappear without an odd cycle. Derived values are free.
pub(super) fn guard_cube(
    c: &Cone,
    values: &[bool],
    proof: &Core,
    b: &mut Budget<'_>,
) -> Result<Cube> {
    debug_assert_eq!(proof.odd_components, 0);
    let mut cube = Cube::new();
    for r in &c.rules {
        b.charge(r.body.len() + 1, "completion guarding cube")?;
        if c.input[r.head]
            || c.fixed[r.head].is_some()
            || r.body
                .iter()
                .any(|(i, p)| c.fixed[*i].is_some_and(|v| v != *p))
        {
            continue;
        }
        // Forward DAG edges and correctly coloured internal edges are safe
        // even when a disabled producer becomes enabled. Only rules that could
        // break this signed topological certificate need a false guard pinned.
        let unsafe_edge = r.body.iter().any(|(i, p)| {
            !c.input[*i]
                && c.fixed[*i].is_none()
                && (proof.component[r.head] > proof.component[*i]
                    || (proof.component[r.head] == proof.component[*i]
                        && proof.colour[r.head].unwrap() ^ !*p != proof.colour[*i].unwrap()))
        });
        if !unsafe_edge {
            continue;
        }
        if let Some((i, _)) = r
            .body
            .iter()
            .find(|(i, p)| c.input[*i] && c.fixed[*i].is_none() && values[*i] != *p)
        {
            cube.insert(*i, values[*i]);
        }
    }
    Ok(cube)
}
