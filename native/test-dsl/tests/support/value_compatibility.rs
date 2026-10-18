//! Compare the unchanged no-value fixtures through the documented bijection.
//! This removes only the new presence/value-copy library steps, never DSL rules,
//! source locations, outcomes or user diagnostics. It does not generate expectations.
#![allow(dead_code)] // Shared structural and replay adapters use different entry points.
use serde_json::Value;
use std::collections::BTreeMap;

fn source_rule(text: &str) -> Option<String> {
    let (index, tail) = text.split_once(':').unwrap();
    let index: usize = index.parse().unwrap();
    match index {
        2 | 3 => None,
        0 | 1 => Some(text.into()),
        _ => Some(format!("{}:{tail}", index - 2)),
    }
}
fn input(text: &str) -> String {
    if let Some(name) = text
        .strip_prefix("value(")
        .and_then(|s| s.strip_suffix(",other_integer)"))
    {
        format!("present({name})")
    } else {
        text.into()
    }
}
fn added_fact(text: &str) -> bool {
    text.starts_with("value(") || text.starts_with("slot_value(")
}

pub fn structure(mut value: Value) -> Value {
    let obj = value.as_object_mut().unwrap();
    let mut addresses = BTreeMap::new();
    for (field, prefix) in [
        ("constants", "constant"),
        ("relations", "relation"),
        ("rules", "rule"),
    ] {
        let old = std::mem::take(obj.get_mut(field).unwrap())
            .as_array()
            .unwrap()
            .clone();
        let mut retained = Vec::new();
        for (i, mut item) in old.into_iter().enumerate() {
            let added = match field {
                "constants" => {
                    let text = item.as_str().unwrap();
                    if text.ends_with(":IntegerCase") {
                        assert_eq!(
                            text, "other_integer:IntegerCase",
                            "compatibility only applies at K empty"
                        );
                        true
                    } else {
                        false
                    }
                }
                "relations" => matches!(item[0].as_str(), Some("value" | "slot_value")),
                "rules" => {
                    item.as_str().unwrap().starts_with("present(")
                        || item.as_str().unwrap().starts_with("slot_value(")
                }
                _ => unreachable!(),
            };
            if !added {
                addresses.insert(
                    format!("{prefix}/{i}"),
                    format!("{prefix}/{}", retained.len()),
                );
                if field == "relations" && item[0] == "present" {
                    item[1] = "Input".into();
                }
                retained.push(item);
            }
        }
        obj.insert(field.into(), retained.into());
    }
    for field in ["origins", "guards", "edits", "owners", "masks"] {
        let old = std::mem::take(obj.get_mut(field).unwrap())
            .as_object()
            .unwrap()
            .clone();
        let mut mapped = serde_json::Map::new();
        for (key, value) in old {
            let end = key
                .split_once('/')
                .map(|(prefix, rest)| {
                    prefix.len() + 1 + rest.find(['/', ':']).unwrap_or(rest.len())
                })
                .unwrap();
            if let Some(address) = addresses.get(&key[..end]) {
                mapped.insert(format!("{address}{}", &key[end..]), value);
            } else {
                assert!(
                    field == "owners" && (key == "rule/2" || key == "rule/3"),
                    "unexpected lost attribution: {key}"
                );
            }
        }
        obj.insert(field.into(), mapped.into());
    }
    value
}

pub fn capture(mut value: Value) -> Value {
    for case in value["cases"].as_array_mut().unwrap() {
        if case.get("worlds").is_none() {
            continue;
        }
        if let Some(s) = case.get_mut("structure") {
            *s = structure(s.take());
        }
        if let Some(rules) = case.get_mut("rules") {
            let old = rules.as_array().unwrap().clone();
            *rules = old
                .into_iter()
                .filter_map(|mut row| {
                    let name = source_rule(row[0].as_str().unwrap())?;
                    row[0] = name.into();
                    Some(row)
                })
                .collect::<Vec<_>>()
                .into();
        }
        if let Some(deps) = case.get_mut("dependencies") {
            let old = deps.as_array().unwrap().clone();
            *deps = old
                .into_iter()
                .filter_map(|mut row| {
                    let name = source_rule(row[2].as_str().unwrap())?;
                    row[2] = name.into();
                    Some(row)
                })
                .collect::<Vec<_>>()
                .into();
        }
        for world in case["worlds"].as_array_mut().unwrap() {
            for fact in world["inputs"].as_array_mut().unwrap() {
                *fact = input(fact.as_str().unwrap()).into();
            }
            for field in ["facts", "evidence"] {
                let data = world[field].as_object_mut().unwrap();
                data.retain(|key, _| !added_fact(key));
                if field == "evidence" {
                    for (fact, evidence) in data.iter_mut() {
                        if fact.starts_with("present(") {
                            *evidence = "input".into();
                            continue;
                        }
                        let Some(row) = evidence.as_array_mut() else {
                            continue;
                        };
                        row[0] = source_rule(row[0].as_str().unwrap()).unwrap().into();
                        for premise in row[1].as_array_mut().unwrap() {
                            if premise[0] == "absent"
                                && premise[1].as_str().unwrap().starts_with("present(")
                            {
                                premise[2] = "input".into();
                            }
                        }
                    }
                }
            }
        }
    }
    value
}
