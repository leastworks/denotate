use denotate_ir_text::{
    ActiveRoot, ProgramMembership, RootInfo, SourceFile, filesystem, load, roots,
};
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::PathBuf,
    sync::atomic::{AtomicUsize, Ordering},
};

fn root(files: &[&str], libraries: &[&str]) -> RootInfo {
    RootInfo {
        files: files.iter().map(|s| (*s).into()).collect(),
        libraries: libraries.iter().map(|s| (*s).into()).collect(),
    }
}

#[test]
fn root_diamonds_and_cycles_preserve_edges_without_duplicating_rules_or_w() {
    let graph = BTreeMap::from([
        ("app".into(), root(&["app.den"], &["left", "right"])),
        ("left".into(), root(&["left.den"], &["common"])),
        ("right".into(), root(&["right.den"], &["common"])),
        ("common".into(), root(&["common.den"], &["app"])),
    ]);
    let membership = ProgramMembership {
        root: "app".into(),
        roots: graph.clone(),
    };
    let sources = [
        SourceFile::new("app.den", 1, "namespace shared; relation r(); r() :- p();"),
        SourceFile::new(
            "common.den",
            1,
            "namespace shared; input p(); assumption w: at_most_one(p, group_by: ());",
        ),
        SourceFile::new("left.den", 1, "namespace left {}"),
        SourceFile::new("right.den", 1, "namespace right {}"),
    ];
    let program = load(&membership, &sources).unwrap();
    assert_eq!(program.documents.len(), 4);
    assert_eq!(program.corpus.rules().count(), 1);
    assert_eq!(program.corpus.assumptions().count(), 1);
    assert_eq!(program.membership.roots, graph);
    for doc in &program.documents {
        assert_eq!(
            doc.ownership,
            if doc.uri == "app.den" {
                "user"
            } else {
                "library"
            }
        );
    }
    let library_check = ProgramMembership {
        root: "common".into(),
        roots: graph,
    };
    let library = load(&library_check, &sources).unwrap();
    assert_eq!(
        library
            .documents
            .iter()
            .find(|d| d.uri == "common.den")
            .unwrap()
            .ownership,
        "user"
    );
    assert_eq!(
        library
            .documents
            .iter()
            .find(|d| d.uri == "app.den")
            .unwrap()
            .ownership,
        "library"
    );
    assert_eq!(
        roots(&[membership, library_check]).unwrap()["common.den"],
        ActiveRoot::NeedsSelection(vec!["app".into(), "common".into()])
    );
}

#[test]
fn authoritative_snapshots_are_deduplicated_and_conflicts_or_missing_members_fail() {
    let file = SourceFile::new("file:///a.den", 1, "relation p(); p();");
    let membership = ProgramMembership::single("root", [file.uri.clone(), file.uri.clone()]);
    let p = load(&membership, &[file.clone(), file.clone()]).unwrap();
    assert_eq!(p.corpus.rules().count(), 1);
    assert_eq!(p.documents.len(), 1);
    for conflicting in [
        SourceFile::new(&file.uri, 2, file.text.clone()),
        SourceFile::new(&file.uri, 1, "relation q();"),
    ] {
        assert!(
            load(&membership, &[file.clone(), conflicting]).unwrap_err()[0]
                .message
                .contains("Conflicting snapshots")
        );
    }
    assert!(
        load(&membership, &[]).unwrap_err()[0]
            .message
            .contains("Missing member snapshot")
    );
    let missing = ProgramMembership {
        root: "missing".into(),
        roots: BTreeMap::new(),
    };
    assert!(
        load(&missing, &[]).unwrap_err()[0]
            .message
            .contains("Missing root")
    );
    let empty = ProgramMembership::single("empty", []);
    assert_eq!(load(&empty, &[]).unwrap().corpus.rules().count(), 0);
    assert_eq!(
        roots(&[membership]).unwrap()[&file.uri],
        ActiveRoot::Selected("root".into())
    );
}

struct Folder(PathBuf);
impl Folder {
    fn new() -> Self {
        static NEXT: AtomicUsize = AtomicUsize::new(0);
        let path = std::env::temp_dir().join(format!(
            "spyne-den-roots-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        Self(path)
    }
    fn write(&self, name: &str, text: &str) {
        let path = self.0.join(name);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, text).unwrap();
    }
}
impl Drop for Folder {
    fn drop(&mut self) {
        fs::remove_dir_all(&self.0).unwrap();
    }
}

#[test]
fn disk_membership_stops_at_nested_roots_and_resolves_relative_libraries_once() {
    let folder = Folder::new();
    folder.write(
        "app/den.root",
        r#"{"libraries":["../lib/den.root", "../lib/./den.root", "nested/den.root"]}"#,
    );
    folder.write("app/deep/user file.den", "namespace n; lib::r();");
    folder.write("app/ignored.txt", "invalid text");
    folder.write("app/unselected/den.root", "broken JSON");
    folder.write("app/unselected/broken.den", "invalid .den syntax");
    folder.write("app/nested/den.root", "{}");
    folder.write("app/nested/member.den", "namespace lib; relation r();");
    folder.write("lib/den.root", r#"{"libraries":["../app/den.root"]}"#);
    folder.write("lib/library.den", "namespace lib; r();");
    let (membership, sources) = filesystem::discover(&folder.0.join("app")).unwrap();
    assert_eq!(membership.roots.len(), 3);
    assert_eq!(membership.roots[&membership.root].files.len(), 1);
    assert_eq!(membership.roots[&membership.root].libraries.len(), 2);
    assert_eq!(sources.len(), 3);
    assert!(sources.iter().any(|s| s.uri.ends_with("user%20file.den")));
    let program = load(&membership, &sources).unwrap();
    assert_eq!(program.corpus.rules().count(), 2);
    assert_eq!(
        program
            .documents
            .iter()
            .filter(|d| d.ownership == "user")
            .count(),
        1
    );
    let (again, reordered) = filesystem::discover(&folder.0.join("app/den.root")).unwrap();
    assert_eq!(again, membership);
    assert_eq!(
        sources.iter().map(|s| &s.uri).collect::<Vec<_>>(),
        reordered.iter().map(|s| &s.uri).collect::<Vec<_>>()
    );
    let subset = filesystem::discover(&folder.0.join("app/nested")).unwrap();
    assert_eq!(subset.1.len(), 1);
    assert_eq!(
        subset
            .0
            .members()
            .unwrap()
            .values()
            .collect::<BTreeSet<_>>(),
        BTreeSet::from([&"user".to_owned()])
    );
}

#[test]
fn manifests_reject_unknown_fields_wrong_shapes_and_unresolvable_roots() {
    let folder = Folder::new();
    for text in [
        "not json",
        "[]",
        r#"{"include":[]}"#,
        r#"{"libraries":null}"#,
        r#"{"libraries":[3]}"#,
        r#"{"libraries":["/absolute/den.root"]}"#,
        r#"{"libraries":["file.den"]}"#,
        r#"{"libraries":["missing/den.root"]}"#,
    ] {
        folder.write("den.root", text);
        assert!(filesystem::discover(&folder.0).is_err(), "{text}");
    }
    folder.write("den.root", "{}");
    let (membership, sources) = filesystem::discover(&folder.0).unwrap();
    assert!(membership.members().unwrap().is_empty());
    assert!(sources.is_empty());
}
