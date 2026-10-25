//! Language-independent workspace-edit mechanics. Frontends own semantic
//! validation, the workspace roots and the snapshot observation stamp.
use crate::{
    document::{line_starts, position},
    Document,
};
use lsp_types::{Range, Url};
use serde_json::{json, Value};
use std::{
    ops::Range as Span,
    path::{Path, PathBuf},
};

pub const DEFAULT_PROTECTED_FOLDERS: &[&str] = &["generated", "node_modules", "dist", ".git"];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EditabilityError {
    NotFile,
    Unavailable,
    Protected,
    OutsideWorkspace,
    PermissionsUnavailable,
    ReadOnly,
}

/// Match complete folder components, including a visible symlink alias.
pub fn protected(path: &Path, folders: &[&str]) -> bool {
    path.components().any(|part| {
        part.as_os_str()
            .to_str()
            .is_some_and(|name| folders.contains(&name))
    })
}

/// Check canonical workspace containment, protected canonical and visible paths,
/// and actual write access. Does not read, write, create or truncate file content.
pub fn editable(uri: &Url, roots: &[PathBuf], folders: &[&str]) -> Result<(), EditabilityError> {
    let visible = uri.to_file_path().map_err(|_| EditabilityError::NotFile)?;
    let path = visible
        .canonicalize()
        .map_err(|_| EditabilityError::Unavailable)?;
    let mut inside = false;
    for root in roots {
        let Ok(canonical) = root.canonicalize() else {
            continue;
        };
        if let Ok(relative) = path.strip_prefix(&canonical) {
            if relative.as_os_str().is_empty() {
                continue;
            }
            inside = true;
            if protected(relative, folders)
                || visible
                    .strip_prefix(root)
                    .is_ok_and(|p| protected(p, folders))
            {
                return Err(EditabilityError::Protected);
            }
        }
    }
    if !inside {
        return Err(EditabilityError::OutsideWorkspace);
    }
    let permissions = path
        .metadata()
        .map_err(|_| EditabilityError::PermissionsUnavailable)?
        .permissions();
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        if permissions.mode() & 0o222 == 0 {
            return Err(EditabilityError::ReadOnly);
        }
    }
    if permissions.readonly() {
        return Err(EditabilityError::ReadOnly);
    }
    // Check actual access too (ACLs can be stricter than mode bits); never truncate.
    std::fs::OpenOptions::new()
        .write(true)
        .open(&path)
        .map_err(|_| EditabilityError::ReadOnly)?;
    Ok(())
}

#[derive(Clone, Debug)]
pub struct Edit {
    pub span: Span<usize>,
    pub text: String,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct OverlappingEdit;

/// Map an original byte anchor through nonoverlapping edits in original byte
/// coordinates. Contained edits grow/shrink the anchor; partial overlaps fail.
/// Insertions at the start shift the anchor, and insertions at its end are outside.
/// The caller validates edit spans and byte boundaries against the source snapshot.
pub fn mapped_span(span: &Span<usize>, edits: &[Edit]) -> Result<Span<usize>, OverlappingEdit> {
    let mut start = span.start as isize;
    let mut end = span.end as isize;
    for edit in edits {
        let delta = edit.text.len() as isize - edit.span.len() as isize;
        if edit.span.end <= span.start {
            start += delta;
            end += delta;
        } else if edit.span.start >= span.end {
            continue;
        } else if edit.span.start >= span.start && edit.span.end <= span.end {
            end += delta;
        } else {
            return Err(OverlappingEdit);
        }
    }
    Ok(start as usize..end as usize)
}

/// A borrowed, immutable source snapshot and its proposed edits. No filesystem
/// lookup is performed: an open buffer must supply its authoritative text/version.
pub struct FileEdits<'a> {
    pub uri: &'a str,
    pub text: &'a str,
    pub version: i32,
    pub open: bool,
    pub edits: &'a [Edit],
}
impl<'a> FileEdits<'a> {
    pub fn new(uri: &'a str, document: &'a Document, edits: &'a [Edit]) -> Self {
        Self {
            uri,
            text: &document.text,
            version: document.version,
            open: document.open,
            edits,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct StaleSnapshot;

/// Assemble versioned documentChanges against the observed source snapshots.
/// Open documents retain their client version; closed documents use null.
/// Compare the frontend's opaque observation stamp after assembly, immediately
/// before returning edits. The frontend includes every relevant dependency in
/// that stamp and must return the result without an intervening state mutation.
pub fn assemble<'a, S: PartialEq>(
    files: impl IntoIterator<Item = FileEdits<'a>>,
    observed: &S,
    current: impl FnOnce() -> S,
) -> Result<Value, StaleSnapshot> {
    let changes = files.into_iter().map(|file| {
        let lines = line_starts(file.text);
        json!({"textDocument":{"uri":file.uri,"version":file.open.then_some(file.version)},
            "edits":file.edits.iter().map(|edit| json!({
                "range":Range::new(position(file.text, &lines, edit.span.start), position(file.text, &lines, edit.span.end)),
                "newText":edit.text
            })).collect::<Vec<_>>()})
    }).collect::<Vec<_>>();
    let result = json!({"documentChanges":changes});
    if observed != &current() {
        return Err(StaleSnapshot);
    }
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::{
        cell::Cell,
        fs,
        sync::atomic::{AtomicU64, Ordering},
    };

    struct Workspace(PathBuf);
    impl Workspace {
        fn new() -> Self {
            static NEXT: AtomicU64 = AtomicU64::new(0);
            let path = std::env::temp_dir().join(format!(
                "denotate-edits-{}-{}",
                std::process::id(),
                NEXT.fetch_add(1, Ordering::Relaxed)
            ));
            fs::create_dir(&path).unwrap();
            Self(path)
        }
        fn file(&self, relative: &str) -> Url {
            let path = self.0.join(relative);
            fs::create_dir_all(path.parent().unwrap()).unwrap();
            fs::write(&path, "keep this content").unwrap();
            Url::from_file_path(path).unwrap()
        }
        fn check(&self, uri: &Url) -> Result<(), EditabilityError> {
            editable(
                uri,
                std::slice::from_ref(&self.0),
                DEFAULT_PROTECTED_FOLDERS,
            )
        }
    }
    impl Drop for Workspace {
        fn drop(&mut self) {
            fs::remove_dir_all(&self.0).unwrap();
        }
    }

    #[test]
    fn editable_checks_containment_policy_and_preserves_bytes() {
        let workspace = Workspace::new();
        let uri = workspace.file("src/program.any");
        assert_eq!(workspace.check(&uri), Ok(()));
        assert_eq!(
            fs::read(uri.to_file_path().unwrap()).unwrap(),
            b"keep this content"
        );
        for folder in DEFAULT_PROTECTED_FOLDERS {
            assert_eq!(
                workspace.check(&workspace.file(&format!("{folder}/file"))),
                Err(EditabilityError::Protected)
            );
        }
        let custom = workspace.file("output/file");
        assert_eq!(workspace.check(&custom), Ok(()));
        assert_eq!(
            editable(&custom, std::slice::from_ref(&workspace.0), &["output"]),
            Err(EditabilityError::Protected)
        );
        // A supplied policy replaces the default, and matches whole components.
        assert_eq!(
            editable(
                &workspace.file("dist/file"),
                std::slice::from_ref(&workspace.0),
                &[]
            ),
            Ok(())
        );
        assert_eq!(workspace.check(&workspace.file("dist-copy/file")), Ok(()));
        let outside = Workspace::new();
        assert_eq!(
            workspace.check(&outside.file("file")),
            Err(EditabilityError::OutsideWorkspace)
        );
        assert_eq!(
            workspace.check(&Url::parse("untitled:buffer").unwrap()),
            Err(EditabilityError::NotFile)
        );
        assert_eq!(
            workspace.check(&Url::from_file_path(workspace.0.join("missing")).unwrap()),
            Err(EditabilityError::Unavailable)
        );
    }

    #[cfg(unix)]
    #[test]
    fn editable_checks_canonical_targets_visible_aliases_and_read_only_files() {
        use std::os::unix::fs::{symlink, PermissionsExt};
        let workspace = Workspace::new();
        let outside = Workspace::new();
        let ordinary = workspace.file("src/file");
        let generated = workspace.file("generated/file");
        let external = outside.file("file");
        for (alias, target, error) in [
            (
                "src/generated-alias",
                generated,
                EditabilityError::Protected,
            ),
            (
                "generated/ordinary-alias",
                ordinary.clone(),
                EditabilityError::Protected,
            ),
            (
                "src/outside-alias",
                external,
                EditabilityError::OutsideWorkspace,
            ),
        ] {
            let path = workspace.0.join(alias);
            symlink(target.to_file_path().unwrap(), &path).unwrap();
            assert_eq!(
                workspace.check(&Url::from_file_path(path).unwrap()),
                Err(error)
            );
        }
        let path = ordinary.to_file_path().unwrap();
        let original = fs::metadata(&path).unwrap().permissions();
        fs::set_permissions(&path, fs::Permissions::from_mode(0o444)).unwrap();
        let result = workspace.check(&ordinary);
        fs::set_permissions(&path, original).unwrap();
        assert_eq!(result, Err(EditabilityError::ReadOnly));
        assert_eq!(fs::read(path).unwrap(), b"keep this content");
    }

    fn edit(span: Span<usize>, text: &str) -> Edit {
        Edit {
            span,
            text: text.into(),
        }
    }

    #[test]
    fn span_mapping_shifts_grows_shrinks_and_rejects_partial_overlaps() {
        // Deltas use UTF-8 bytes, not scalar or UTF-16 counts.
        let edits = [
            edit(1..3, "😀"),
            edit(5..7, "é😀"),
            edit(8..10, ""),
            edit(12..13, "after"),
        ];
        assert_eq!(mapped_span(&(4..11), &edits), Ok(6..15));
        assert_eq!(mapped_span(&(5..7), &edits), Ok(7..13));
        assert_eq!(mapped_span(&(4..6), &edits), Err(OverlappingEdit));
        assert_eq!(mapped_span(&(6..8), &edits), Err(OverlappingEdit));
        assert_eq!(
            mapped_span(&(6..6), &[edit(5..7, "x")]),
            Err(OverlappingEdit)
        );
        assert_eq!(
            mapped_span(&(4..8), &[edit(4..4, "a"), edit(8..8, "z")]),
            Ok(5..9)
        );
        assert_eq!(
            mapped_span(&(4..8), &[edit(2..4, ""), edit(8..10, "z")]),
            Ok(2..6)
        );
    }

    #[test]
    fn assembly_uses_snapshot_positions_and_open_client_versions() {
        let edits = [edit(2..6, "new"), edit(8..9, "next")];
        let files = [true, false].map(|open| FileEdits {
            uri: if open {
                "file:///open"
            } else {
                "file:///closed"
            },
            text: "é😀\r\nx",
            version: 42,
            open,
            edits: &edits,
        });
        let output = assemble(files, &7, || 7).unwrap();
        let changes = output["documentChanges"].as_array().unwrap();
        assert_eq!(
            changes[0]["textDocument"],
            json!({"uri":"file:///open","version":42})
        );
        assert_eq!(
            changes[1]["textDocument"],
            json!({"uri":"file:///closed","version":null})
        );
        for change in changes {
            assert_eq!(
                change["edits"],
                json!([
                    {"range":{"start":{"line":0,"character":1},"end":{"line":0,"character":3}},"newText":"new"},
                    {"range":{"start":{"line":1,"character":0},"end":{"line":1,"character":1}},"newText":"next"}
                ])
            );
        }
    }

    #[test]
    fn assembly_checks_the_stamp_after_consuming_all_snapshots() {
        let stamp = Cell::new(7);
        let files = std::iter::once_with(|| {
            stamp.set(8);
            FileEdits {
                uri: "file:///file",
                text: "",
                version: 1,
                open: true,
                edits: &[],
            }
        });
        assert_eq!(assemble(files, &7, || stamp.get()), Err(StaleSnapshot));
    }
}
