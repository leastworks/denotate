//! Window-wide policy, independent of document buffers and checker sessions.
use denotate_check::{DeterministicLimits, Limits, OperationalLimits};
use serde_json::{json, Value};
use std::time::Duration;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Config {
    pub timeout_ms: u64,
    pub limits: DeterministicLimits,
    pub show_library_rewrites: bool,
    pub checking_within_w: bool,
}
impl Default for Config {
    fn default() -> Self {
        let limits = Limits::default();
        Self {
            timeout_ms: limits.timeout.as_millis().try_into().unwrap_or(u64::MAX),
            limits: (&limits).into(),
            show_library_rewrites: true,
            checking_within_w: false,
        }
    }
}
impl Config {
    pub fn read(value: &Value) -> Result<Self, String> {
        let mut config = Self::default();
        if !value.is_null() && !value.is_object() {
            return Err("Expected a denotate configuration object".into());
        }
        if let Some(v) = value.get("timeoutMs") {
            config.timeout_ms = v.as_u64().ok_or("Expected nonnegative integer timeoutMs")?;
        }
        if let Some(v) = value.get("showLibraryRewrites") {
            config.show_library_rewrites =
                v.as_bool().ok_or("Expected boolean showLibraryRewrites")?;
        }
        if let Some(v) = value.get("checkingWithinW") {
            config.checking_within_w = v.as_bool().ok_or("Expected boolean checkingWithinW")?;
        }
        if let Some(limits) = value.get("limits") {
            for (name, value) in limits.as_object().ok_or("Expected a limits object")? {
                let n = value
                    .as_u64()
                    .and_then(|n| usize::try_from(n).ok())
                    .ok_or_else(|| {
                        format!("Expected nonnegative integer limits.{name} fitting in usize")
                    })?;
                let target = match name.as_str() {
                    "maxAtoms" => &mut config.limits.max_atoms,
                    "maxRules" => &mut config.limits.max_rules,
                    "maxDependencies" => &mut config.limits.max_dependencies,
                    "maxWork" => &mut config.limits.max_work,
                    "maxBddVariables" => &mut config.limits.max_bdd_variables,
                    "maxBddNodes" => &mut config.limits.max_bdd_nodes,
                    "maxBddTasks" => &mut config.limits.max_bdd_tasks,
                    "maxConditionNodes" => &mut config.limits.max_condition_nodes,
                    "maxStructuralSplitDepth" => &mut config.limits.max_structural_split_depth,
                    "maxStructuralSplitLeaves" => &mut config.limits.max_structural_split_leaves,
                    "maxStructuralSplitScoringWork" => {
                        &mut config.limits.max_structural_split_scoring_work
                    }
                    "maxStructuralSplitWork" => &mut config.limits.max_structural_split_work,
                    _ => return Err(format!("Unknown limit {name}")),
                };
                *target = n;
            }
        }
        Ok(config)
    }
    pub fn checker_limits(&self) -> Limits {
        self.limits.with_operations(&OperationalLimits {
            run_deadline: None,
            profile: Default::default(),
            progress: Default::default(),
            cancellation: Default::default(),
            timeout: Duration::from_millis(self.timeout_ms),
        })
    }
    pub fn data(&self) -> Value {
        json!({"timeoutMs":self.timeout_ms,"showLibraryRewrites":self.show_library_rewrites,"checkingWithinW":self.checking_within_w,
        "limits":{
            "maxAtoms":self.limits.max_atoms,"maxRules":self.limits.max_rules,
            "maxDependencies":self.limits.max_dependencies,"maxWork":self.limits.max_work,
            "maxBddVariables":self.limits.max_bdd_variables,"maxBddNodes":self.limits.max_bdd_nodes,
            "maxBddTasks":self.limits.max_bdd_tasks,"maxConditionNodes":self.limits.max_condition_nodes,
            "maxStructuralSplitWork":self.limits.max_structural_split_work,
            "maxStructuralSplitScoringWork":self.limits.max_structural_split_scoring_work,
            "maxStructuralSplitLeaves":self.limits.max_structural_split_leaves,
            "maxStructuralSplitDepth":self.limits.max_structural_split_depth
        }})
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn overrides_round_trip_all_limits_and_omissions_restore_checker_defaults() {
        let defaults = Config::default();
        assert_eq!(Config::read(&json!({})).unwrap(), defaults);
        for name in defaults.data()["limits"].as_object().unwrap().keys() {
            let config = Config::read(&json!({"timeoutMs":0,"limits":{name:0}})).unwrap();
            let actual = DeterministicLimits::from(&config.checker_limits());
            assert_eq!(actual, config.limits);
            assert_eq!(config.data()["limits"][name], 0);
            assert!(config.checker_limits().timeout.is_zero());
            assert_ne!(config, defaults);
            assert_eq!(Config::read(&config.data()).unwrap(), config);
        }
        assert_eq!(Config::read(&Value::Null).unwrap(), defaults);
    }
    #[test]
    fn editor_settings_schema_matches_checker_defaults_and_limit_names() {
        let package: Value =
            serde_json::from_str(include_str!("../../../editors/den/package.json")).unwrap();
        let properties = &package["contributes"]["configuration"]["properties"];
        let defaults = Config::default().data();
        assert_eq!(
            properties["denotate.timeoutMs"]["default"],
            defaults["timeoutMs"]
        );
        assert_eq!(
            properties["denotate.checkingWithinW"]["default"],
            defaults["checkingWithinW"]
        );
        assert!(!Config::default().checking_within_w);
        let enabled = Config::read(&json!({"checkingWithinW":true})).unwrap();
        assert!(enabled.checking_within_w);
        assert_eq!(Config::read(&enabled.data()).unwrap(), enabled);
        let schema = properties["denotate.limits"]["properties"]
            .as_object()
            .unwrap();
        let names = defaults["limits"].as_object().unwrap();
        assert!(schema.keys().eq(names.keys()), "{schema:?}");
    }
    #[test]
    fn malformed_limits_are_rejected_as_a_whole() {
        for config in [
            json!({"checkingWithinW":"true"}),
            json!({"checkingWithinW":null}),
            json!({"limits":null}),
            json!({"limits":[]}),
            json!({"limits":{"maxAtoms":-1}}),
            json!({"limits":{"maxAtoms":1.5}}),
            json!({"limits":{"maxAtoms":"4"}}),
            json!({"limits":{"maxAtoms":1,"maxAtms":2}}),
            json!({"timeoutMs":false}),
            json!({"timeoutMs":-1}),
        ] {
            assert!(Config::read(&config).is_err(), "{config}");
        }
    }
}
