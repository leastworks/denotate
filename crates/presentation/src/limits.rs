use denotate_check::LimitDetails;
use serde_json::{Value, json};

/// Add diagnostic-only fields without changing existing phase/resource names.
pub fn with_limit_details(mut data: Value, details: LimitDetails) -> Value {
    if let Some(subphase) = details.subphase {
        data["subphase"] = json!(subphase);
    }
    if let Some(limit) = details.limit {
        data["limit"] = json!(limit);
    }
    if let Some(observed) = details.observed {
        data["observed"] = json!(observed);
    }
    data
}
pub fn exhaustion_data(phase: &str, resource: &str, details: LimitDetails) -> Value {
    with_limit_details(json!({"phase":phase,"resource":resource}), details)
}
pub fn exhaustion_text(phase: &str, resource: &str, details: LimitDetails) -> String {
    text(
        phase,
        resource,
        details.subphase,
        details.limit,
        details.observed,
    )
}
fn text(
    phase: &str,
    resource: &str,
    subphase: Option<&str>,
    limit: Option<usize>,
    observed: Option<usize>,
) -> String {
    let stage = subphase.map_or_else(|| phase.to_owned(), |s| format!("{phase} / {s}"));
    let mut text = if resource == "deadline" {
        format!("{stage} reached its deadline")
    } else {
        format!("{stage} exhausted its {resource} budget")
    };
    if let Some(limit) = limit {
        text.push_str(&format!(
            " (limit {limit}{}",
            if resource == "deadline" { " ms" } else { "" }
        ));
        if let Some(observed) = observed {
            text.push_str(&format!(", observed demand {observed}"));
        }
        text.push(')');
    }
    text
}

/// Render the resource reasons already present in a published summary. Includes
/// advisory/attribution limits; a message is not a new verdict or finding.
pub fn exhaustion_messages(summary: &Value) -> std::collections::BTreeSet<String> {
    fn visit(value: &Value, messages: &mut std::collections::BTreeSet<String>) {
        match value {
            Value::Object(fields) => {
                if let (Some(phase), Some(resource)) =
                    (value["phase"].as_str(), value["resource"].as_str())
                {
                    let number = |key| value[key].as_u64().and_then(|n| usize::try_from(n).ok());
                    messages.insert(text(
                        phase,
                        resource,
                        value["subphase"].as_str(),
                        number("limit"),
                        number("observed"),
                    ));
                }
                for child in fields.values() {
                    visit(child, messages);
                }
            }
            Value::Array(items) => {
                for child in items {
                    visit(child, messages);
                }
            }
            _ => {}
        }
    }
    let mut messages = std::collections::BTreeSet::new();
    visit(summary, &mut messages);
    messages
}
