//! Disk adapter for commands. The core loader only consumes caller-supplied
//! membership and snapshots; editor integrations need not use this adapter.
use crate::{Diagnostic, ProgramMembership, Result, RootInfo, SourceFile};
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Path, PathBuf},
};

pub fn uri(path: &Path) -> String {
    let escaped = path
        .as_os_str()
        .as_encoded_bytes()
        .iter()
        .map(|b| {
            if b.is_ascii_alphanumeric() || b"/._~-:".contains(b) {
                (*b as char).to_string()
            } else {
                format!("%{b:02X}")
            }
        })
        .collect::<String>();
    format!("file://{escaped}")
}
fn failure(path: &Path, message: impl ToString) -> Vec<Diagnostic> {
    vec![Diagnostic {
        uri: uri(path),
        range: 0..0,
        message: message.to_string(),
    }]
}
fn io<T>(path: &Path, result: std::io::Result<T>) -> Result<T> {
    result.map_err(|e| failure(path, e))
}
fn manifest(path: &Path) -> Result<PathBuf> {
    let path = if path.is_dir() {
        path.join("den.root")
    } else {
        path.to_owned()
    };
    if path.file_name().is_none_or(|n| n != "den.root") {
        return Err(failure(
            &path,
            "Expected a den.root manifest or its containing folder",
        ));
    }
    io(&path, fs::canonicalize(&path))
}
fn members(folder: &Path, out: &mut BTreeMap<String, PathBuf>) -> Result<()> {
    let entries = io(folder, fs::read_dir(folder))?;
    for entry in entries {
        let entry = io(folder, entry)?;
        let path = entry.path();
        let kind = io(&path, entry.file_type())?;
        // Do not follow directory symlinks: membership follows folder boundaries.
        if kind.is_dir() {
            if !path
                .join("den.root")
                .try_exists()
                .map_err(|e| failure(&path, e))?
            {
                members(&path, out)?;
            }
        } else if path.extension().is_some_and(|e| e == "den") && path.is_file() {
            let canonical = io(&path, fs::canonicalize(&path))?;
            out.insert(uri(&canonical), canonical);
        }
    }
    Ok(())
}

/// Shared manifest validation for disk commands and authoritative editor snapshots.
pub fn manifest_libraries(text: &str) -> std::result::Result<Vec<PathBuf>, String> {
    let json: serde_json::Value = serde_json::from_str(text).map_err(|e| e.to_string())?;
    let object = json.as_object().ok_or("den.root must be a JSON object")?;
    if object.keys().any(|k| k != "libraries") {
        return Err("Unknown den.root field; only libraries is supported".into());
    }
    let Some(value) = object.get("libraries") else {
        return Ok(vec![]);
    };
    let values = value
        .as_array()
        .ok_or("libraries must be an array of relative den.root paths")?;
    values
        .iter()
        .map(|value| {
            let relative = PathBuf::from(value.as_str().ok_or("A library path must be a string")?);
            if relative.is_absolute() || relative.file_name().is_none_or(|n| n != "den.root") {
                return Err("A library path must be relative and end in den.root".into());
            }
            Ok(relative)
        })
        .collect()
}

/// Discover the selected root and reachable library roots. Directory traversal
/// stops at nested `den.root` files. Repeated paths and cycles are canonicalized
/// and visited once; the returned graph retains every dependency edge.
pub fn discover(root: &Path) -> Result<(ProgramMembership, Vec<SourceFile>)> {
    let selected = manifest(root)?;
    let mut pending = vec![selected.clone()];
    let mut roots = BTreeMap::new();
    let mut files = BTreeMap::new();
    while let Some(path) = pending.pop() {
        let identity = uri(&path);
        if roots.contains_key(&identity) {
            continue;
        }
        let text = io(&path, fs::read_to_string(&path))?;
        let folder = path.parent().expect("a canonical file has a parent");
        let mut libraries = BTreeSet::new();
        for relative in manifest_libraries(&text).map_err(|e| failure(&path, e))? {
            let target = manifest(&folder.join(relative))?;
            libraries.insert(uri(&target));
            pending.push(target);
        }
        let mut own_files = BTreeMap::new();
        members(folder, &mut own_files)?;
        roots.insert(
            identity,
            RootInfo {
                files: own_files.keys().cloned().collect(),
                libraries,
            },
        );
        files.extend(own_files);
    }
    let sources = files
        .into_iter()
        .map(|(uri, path)| {
            Ok(SourceFile::new(
                uri,
                1,
                io(&path, fs::read_to_string(&path))?,
            ))
        })
        .collect::<Result<_>>()?;
    Ok((
        ProgramMembership {
            root: uri(&selected),
            roots,
        },
        sources,
    ))
}

/// Command-only resolver. Editors supply their own authoritative-buffer resolver.
pub struct FileOriginResolver;
impl crate::origins::OriginResolver for FileOriginResolver {
    fn resolve(
        &mut self,
        source: &crate::origins::SourceIdentity,
    ) -> std::result::Result<std::sync::Arc<str>, crate::origins::Unavailable> {
        use crate::origins::Unavailable;
        let path = source.uri.strip_prefix("file://").ok_or_else(|| {
            Unavailable::Inaccessible("Non-file URI; supply a caller resolver".into())
        })?;
        let path = path
            .strip_prefix("localhost/")
            .map(|p| format!("/{p}"))
            .unwrap_or_else(|| path.to_owned());
        if !path.starts_with('/') {
            return Err(Unavailable::Inaccessible("Nonlocal file URI".into()));
        }
        let mut bytes = Vec::new();
        let mut i = 0;
        while i < path.len() {
            if path.as_bytes()[i] == b'%' {
                let pair = path
                    .get(i + 1..i + 3)
                    .ok_or_else(|| Unavailable::Inaccessible("Invalid URI escape".into()))?;
                bytes.push(
                    u8::from_str_radix(pair, 16)
                        .map_err(|_| Unavailable::Inaccessible("Invalid URI escape".into()))?,
                );
                i += 3;
            } else {
                bytes.push(path.as_bytes()[i]);
                i += 1;
            }
        }
        #[cfg(unix)]
        let path = {
            use std::os::unix::ffi::OsStringExt;
            PathBuf::from(std::ffi::OsString::from_vec(bytes))
        };
        #[cfg(not(unix))]
        let path = PathBuf::from(
            String::from_utf8(bytes)
                .map_err(|_| Unavailable::Inaccessible("Invalid UTF-8 path".into()))?,
        );
        fs::read_to_string(path).map(Into::into).map_err(|e| {
            if e.kind() == std::io::ErrorKind::NotFound {
                Unavailable::Missing
            } else {
                Unavailable::Inaccessible(e.to_string())
            }
        })
    }
}
