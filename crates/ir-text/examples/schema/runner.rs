use super::{check_options, generate::*};
use serde_json::{Value, json};
use std::{
    collections::BTreeMap,
    fs,
    io::{BufRead, BufReader, BufWriter, Write},
    path::{Path, PathBuf},
    process::{Command, Stdio},
    time::{Instant, SystemTime, UNIX_EPOCH},
};

const HELP: &str = "Usage: just bench-den-schema [OPTIONS] [-- CHECKER_LIMITS...]\n\n\
--out DIR                 New persistent run directory (default target/bench-den-schema/<timestamp>)\n\
--encoding NAME           ambiguous | coverage (default) | negated | assumed\n\
--topology NAME           independent (default) | coupled | mixed | layered\n\
--coupling-percent N      Layered conditions with cross reads (0..100; default 50)\n\
--fields N                Total message fields, including selectors (default 6)\n\
--reads N                 Payload fields read by terms, in addition to selectors (default 2)\n\
--depth N --width N        Format tree (defaults 1, 2)\n\
--shadowed N              Redundant conditional declarations (default 2)\n\
--wide-heads N --producers N   Number of wide heads / producers per head (defaults 0, 0)\n\
--computed N              Separate computed elements (default 1)\n\
--catalog N --catalog-layers N   Fixed catalog entries / propagation layers (defaults 4, 2)\n\
--overlaps                Inject sibling overlaps (ordinary verdicts are then not promised)\n\
--samply                  Also save a CPU recording; requires samply on PATH\n\
--source FILE             Use an authored source (shared shape-zoo runner)\n\
--generate-only           Save sources and configuration without invoking check\n\
--summarize DIR           Rebuild report.json from an interrupted run's saved files\n\
\nLimits after -- are the check-den resource flags, e.g. --max-atoms 2000000.\n\
No limits are raised implicitly. Exit 0 means the benchmark recorded a run,\n\
not that the generated program proved; see checkerExitCode and outcomes.\n";

pub fn run(args: Vec<String>) -> Result<(), String> {
    if args.iter().any(|a| matches!(a.as_str(), "--help" | "-h")) {
        print!("{HELP}");
        return Ok(());
    }
    if let [mode, dir] = args.as_slice() {
        if mode == "--summarize" {
            return summarize(Path::new(dir));
        }
    }
    let mut shape = Shape::default();
    let mut out = None;
    let mut source_path = None;
    let mut sampled = false;
    let mut generate_only = false;
    let mut forwarded = Vec::new();
    let mut args = args.into_iter();
    let mut seen = std::collections::BTreeSet::new();
    while let Some(arg) = args.next() {
        if arg == "--" {
            forwarded.extend(args);
            break;
        }
        if !seen.insert(arg.clone()) {
            return Err(format!("repeated option {arg}"));
        }
        match arg.as_str() {
            "--overlaps" => {
                shape.overlaps = true;
                continue;
            }
            "--samply" => {
                sampled = true;
                continue;
            }
            "--generate-only" => {
                generate_only = true;
                continue;
            }
            _ => {}
        }
        let value = args.next().ok_or_else(|| format!("{arg} needs a value"))?;
        match arg.as_str() {
            "--out" => out = Some(PathBuf::from(value)),
            "--source" => source_path = Some(PathBuf::from(value)),
            "--encoding" => shape.encoding = Encoding::parse(&value)?,
            "--topology" => shape.topology = Topology::parse(&value)?,
            _ => {
                let target = match arg.as_str() {
                    "--fields" => &mut shape.fields,
                    "--reads" => &mut shape.reads,
                    "--coupling-percent" => &mut shape.coupling_percent,
                    "--depth" => &mut shape.depth,
                    "--width" => &mut shape.width,
                    "--shadowed" => &mut shape.shadowed,
                    "--wide-heads" => &mut shape.wide_heads,
                    "--producers" => &mut shape.producers,
                    "--computed" => &mut shape.computed,
                    "--catalog" => &mut shape.catalog,
                    "--catalog-layers" => &mut shape.catalog_layers,
                    _ => return Err(format!("unknown option {arg}; use --help")),
                };
                *target = value
                    .parse()
                    .map_err(|_| format!("{arg} needs a nonnegative integer"))?;
            }
        }
    }
    shape.validate()?;
    let flags = check_options::limit_values(&denotate_check::Limits::default());
    if forwarded.len() % 2 != 0
        || forwarded
            .chunks(2)
            .any(|p| !flags.iter().any(|(flag, _)| *flag == p[0]))
    {
        return Err("after --, supply only check-den limit flags and their values".into());
    }
    let parsed = check_options::Options::parse(
        std::iter::once("program".into()).chain(forwarded.clone()),
        Default::default(),
    )
    .map_err(|(_, e)| e)?;
    let limits: BTreeMap<_, _> = check_options::limit_values(&parsed.limits)
        .into_iter()
        .collect();
    let dir = out.unwrap_or_else(|| {
        PathBuf::from(format!(
            "target/bench-den-schema/{}",
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ))
    });
    if let Some(parent) = dir.parent().filter(|p| !p.as_os_str().is_empty()) {
        fs::create_dir_all(parent).map_err(|e| e.to_string())?;
    }
    fs::create_dir(&dir)
        .map_err(|e| format!("cannot create new run directory {}: {e}", dir.display()))?;
    let dir = fs::canonicalize(dir).map_err(|e| e.to_string())?;
    fs::create_dir(dir.join("program")).map_err(|e| e.to_string())?;
    fs::write(dir.join("program/den.root"), "{}\n").map_err(|e| e.to_string())?;
    fs::write(
        dir.join("program/schema.den"),
        if let Some(path) = &source_path {
            fs::read_to_string(path).map_err(|e| e.to_string())?
        } else {
            source(&shape)?
        },
    )
    .map_err(|e| e.to_string())?;
    let binary = std::env::current_exe()
        .map_err(|e| e.to_string())?
        .parent()
        .unwrap()
        .join("check");
    let mut check_args = vec![
        dir.join("program").to_string_lossy().into_owned(),
        "--json".into(),
        "--profile-memory".into(),
        dir.join("memory.jsonl").to_string_lossy().into_owned(),
    ];
    check_args.extend(forwarded);
    let revision = Command::new("git")
        .args(["rev-parse", "HEAD"])
        .output()
        .ok()
        .filter(|o| o.status.success())
        .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_owned());
    let dirty = Command::new("git")
        .args(["diff", "--quiet", "HEAD"])
        .status()
        .ok()
        .map(|s| !s.success());
    let mut manifest = json!({"state":if generate_only {"generated"} else {"running"}, "sourceOverride":source_path,"buildProfile":"profiling", "sampled":sampled, "revision":revision,"trackedChanges":dirty,
        "layout":layout(&shape)?.iter().map(|(step,deps)|json!({"step":format!("{step:?}"),"field":match step {Step::Accept(i)=>Some(format!("f{}",shape.depth+i)), _=>None},"requires":deps.iter().map(|d|format!("{d:?}")).collect::<Vec<_>>(),"acceptanceJustification":matches!(step,Step::Accept(_)).then_some("owner match accepts; owner nonmatch excludes declaration and every subordinate shadow/wide producer")})).collect::<Vec<_>>(),
        "crossReadCount":(0..shape.reads).filter(|i|cross_read(&shape,*i).is_some()).count(),
        "layoutDepth":if shape.topology==Topology::Layered {Some(shape.depth+2)} else {None},
        "shape":{"couplingPercent":shape.coupling_percent,"fields":shape.fields,"reads":shape.reads,"depth":shape.depth,"width":shape.width,"encoding":format!("{:?}",shape.encoding).to_lowercase(),"topology":format!("{:?}",shape.topology).to_lowercase(),"overlaps":shape.overlaps,"shadowed":shape.shadowed,"wideHeads":shape.wide_heads,"producers":shape.producers,"computed":shape.computed,"catalog":shape.catalog,"catalogLayers":shape.catalog_layers},
        "limits":limits,"binary":binary,"checkArgs":check_args});
    if source_path.is_some() {
        for key in ["shape", "layout", "layoutDepth", "crossReadCount"] {
            manifest.as_object_mut().unwrap().remove(key);
        }
    }
    save(&dir.join("run.json"), &manifest)?;
    save(&dir.join("report.json"), &manifest)?;
    eprintln!("Saved run: {}", dir.display());
    if generate_only {
        return Ok(());
    }
    let mut command = if sampled {
        let mut c = Command::new("samply");
        c.args(["record", "--save-only", "--unstable-presymbolicate", "-o"])
            .arg(dir.join("cpu.json.gz"))
            .arg("--")
            .arg(&binary);
        c
    } else {
        Command::new(&binary)
    };
    command
        .args(&check_args)
        .stdin(Stdio::null())
        .stdout(fs::File::create(dir.join("stdout.txt")).map_err(|e| e.to_string())?)
        .stderr(fs::File::create(dir.join("stderr.txt")).map_err(|e| e.to_string())?);
    eprintln!(
        "Running the profiling build; progress is in stderr.txt. Sources and logs survive interruption."
    );
    let started = Instant::now();
    match command.status() {
        Ok(status) => {
            manifest["state"] = json!("finished");
            manifest["launcherExitCode"] = json!(status.code());
            #[cfg(unix)]
            {
                use std::os::unix::process::ExitStatusExt;
                manifest["launcherSignal"] = json!(status.signal());
            }
            manifest["wallMs"] = json!(started.elapsed().as_secs_f64() * 1000.);
        }
        Err(e) => {
            manifest["state"] = json!("launch-failed");
            manifest["launchError"] = json!(e.to_string());
        }
    }
    save(&dir.join("run.json"), &manifest)?;
    summarize(&dir)?;
    if manifest["state"] == "launch-failed" {
        return Err(manifest["launchError"].as_str().unwrap().into());
    }
    Ok(())
}
fn save(path: &Path, value: &Value) -> Result<(), String> {
    let temporary = path.with_extension("json.tmp");
    let mut file = BufWriter::new(fs::File::create(&temporary).map_err(|e| e.to_string())?);
    serde_json::to_writer_pretty(&mut file, value).map_err(|e| e.to_string())?;
    writeln!(file).map_err(|e| e.to_string())?;
    file.flush().map_err(|e| e.to_string())?;
    fs::rename(temporary, path).map_err(|e| e.to_string())
}

pub(super) fn summarize(dir: &Path) -> Result<(), String> {
    let mut report: Value =
        serde_json::from_reader(fs::File::open(dir.join("run.json")).map_err(|e| e.to_string())?)
            .map_err(|e| e.to_string())?;
    let mut phases = Vec::new();
    let mut active = BTreeMap::<u64, Value>::new();
    let mut rounds = BTreeMap::<String, Value>::new();
    let mut malformed = 0;
    if let Ok(file) = fs::File::open(dir.join("memory.jsonl")) {
        for line in BufReader::new(file).lines() {
            let line = line.map_err(|e| e.to_string())?;
            let Ok(v) = serde_json::from_str::<Value>(&line) else {
                malformed += 1;
                continue;
            };
            match v["type"].as_str() {
                Some("profile") => {
                    if let Some(id) = v["span"].as_u64() {
                        if v["event"] == "start" {
                            active.insert(id, v);
                        } else {
                            active.remove(&id);
                            phases.push(v);
                        }
                    }
                }
                Some("progress") => {
                    let d = &v["detail"];
                    if let Some(round) = d["admission"]["round"].as_u64() {
                        rounds.insert(
                            format!(
                                "{}:{}:{round:020}",
                                d["verification"], d["admission"]["phase"]
                            ),
                            d["admission"].clone(),
                        );
                    }
                    if d["phase"] == "admission"
                        && d["ground"].is_object()
                        && d.get("admission").is_none()
                        && d.get("remainingComponent").is_none()
                    {
                        report["beforeAdmission"] = sizes(d);
                    }
                    if d["phase"] == "checking"
                        && d["admitted"].is_boolean()
                        && d.get("checking").is_none()
                    {
                        report["afterAdmission"] = sizes(d);
                        report["afterAdmission"]["admitted"] = d["admitted"].clone();
                        report["afterAdmission"]["unresolvedComponents"] =
                            d["unresolvedComponents"].clone();
                    }
                }
                Some("run-end") => {
                    report["checkerExitCode"] = v["exitCode"].clone();
                    report["checkerError"] = v["error"].clone();
                }
                _ => {}
            }
        }
    }
    let stdout = fs::read_to_string(dir.join("stdout.txt")).unwrap_or_default();
    let mut outcomes = Vec::new();
    for text in stdout.split("Results: ").skip(1) {
        if let Some(Ok(v)) = serde_json::Deserializer::from_str(text)
            .into_iter::<Value>()
            .next()
        {
            outcomes.push(v);
        }
    }
    report["outcomes"] = json!(outcomes);
    report["phases"] = json!(phases);
    report["unfinishedSpans"] = json!(active.into_values().collect::<Vec<_>>());
    report["admissionRounds"] = json!(rounds.into_values().collect::<Vec<_>>());
    report["malformedProfileLines"] = json!(malformed);
    // A missing terminal event is not proof, even when a sampler exits successfully.
    report["checkerFinished"] = json!(report["checkerExitCode"].is_number());
    save(&dir.join("report.json"), &report)?;
    println!("Report: {}", dir.join("report.json").display());
    println!(
        "Checker exit: {}; before: {}; after: {}",
        report["checkerExitCode"],
        report["beforeAdmission"]["ground"],
        report["afterAdmission"]["ground"]
    );
    Ok(())
}

fn sizes(detail: &Value) -> Value {
    // The graph iterator counts surviving residual rules plus retained fixed
    // evidence. The fold inventory also counts removed residual rule slots.
    let active = detail["ground"]["ruleInstances"]
        .as_u64()
        .zip(detail["fold"]["retainedEvidence"]["ruleInstances"].as_u64())
        .and_then(|(total, fixed)| total.checked_sub(fixed));
    json!({"ground":detail["ground"],"fold":detail["fold"],"activeResidualRuleInstances":active})
}
