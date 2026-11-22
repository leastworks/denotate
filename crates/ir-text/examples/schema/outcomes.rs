//! Streaming benchmark summaries: outcomes and reasons remain intact; full
//! evidence stays in stdout.txt. Skip evidence before allocating its JSON tree.
use serde::{
    Deserialize, Deserializer,
    de::{self, MapAccess, SeqAccess, Visitor},
};
use serde_json::{Map, Value};
use std::fmt;

pub(super) struct Compact(pub Value);
impl<'de> Deserialize<'de> for Compact {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        struct Summary;
        impl<'de> Visitor<'de> for Summary {
            type Value = Compact;
            fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.write_str("a JSON outcome")
            }
            fn visit_bool<E: de::Error>(self, v: bool) -> Result<Compact, E> {
                Ok(Compact(v.into()))
            }
            fn visit_i64<E: de::Error>(self, v: i64) -> Result<Compact, E> {
                Ok(Compact(v.into()))
            }
            fn visit_u64<E: de::Error>(self, v: u64) -> Result<Compact, E> {
                Ok(Compact(v.into()))
            }
            fn visit_f64<E: de::Error>(self, v: f64) -> Result<Compact, E> {
                Ok(Compact(v.into()))
            }
            fn visit_str<E: de::Error>(self, v: &str) -> Result<Compact, E> {
                Ok(Compact(v.into()))
            }
            fn visit_string<E: de::Error>(self, v: String) -> Result<Compact, E> {
                Ok(Compact(v.into()))
            }
            fn visit_unit<E: de::Error>(self) -> Result<Compact, E> {
                Ok(Compact(Value::Null))
            }
            fn visit_seq<A: SeqAccess<'de>>(self, mut a: A) -> Result<Compact, A::Error> {
                let mut values = Vec::new();
                while let Some(Compact(v)) = a.next_element()? {
                    values.push(v);
                }
                Ok(Compact(Value::Array(values)))
            }
            fn visit_map<A: MapAccess<'de>>(self, mut a: A) -> Result<Compact, A::Error> {
                let mut values = Map::new();
                while let Some(key) = a.next_key::<String>()? {
                    if key == "evidence" || key == "completionEvidence" {
                        a.next_value::<de::IgnoredAny>()?;
                    } else {
                        values.insert(key, a.next_value::<Compact>()?.0);
                    }
                }
                Ok(Compact(Value::Object(values)))
            }
        }
        d.deserialize_any(Summary)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn summary_preserves_states_counts_and_reasons_but_skips_nested_evidence() {
        let source = serde_json::json!({"completionEvidence":{"models":{"m0":{"interpretation":[1,2,3]}}},"state":"incomplete", "count":3,"complete":false,
            "classification":{"accepted":{"state":"found","evidence":{"interpretation":[1,2,3]}}},
            "findings":[{"kind":"inconclusive","evidence":{"huge":[1,2,3]}}],
            "reason":{"phase":"checking","resource":"work","limit":100,"observed":101},"optional":null});
        let summary: Compact =
            serde_json::from_reader(std::io::Cursor::new(source.to_string())).unwrap();
        let mut expected = source;
        expected
            .as_object_mut()
            .unwrap()
            .remove("completionEvidence");
        expected["classification"]["accepted"]
            .as_object_mut()
            .unwrap()
            .remove("evidence");
        expected["findings"][0]
            .as_object_mut()
            .unwrap()
            .remove("evidence");
        assert_eq!(summary.0, expected);
    }
}
