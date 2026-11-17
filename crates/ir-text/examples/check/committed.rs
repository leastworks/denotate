//! CLI-owned IO. Export failures are diagnostic, never checker verdicts.
use denotate_ir_text::{ProgramMembership, SourceFile};
use sha2::{Digest, Sha256};
use std::{
    fs::{self, File},
    io::{self, BufWriter, Write},
    path::{Path, PathBuf},
    sync::atomic::{AtomicU64, Ordering},
};

pub fn source_digest(
    membership: &ProgramMembership,
    sources: &[SourceFile],
    limits: &denotate_ir_text::committed::ExportLimits,
) -> io::Result<(String, denotate_ir_text::committed::ExportLimits)> {
    let started = std::time::Instant::now();
    let mut remaining = limits.clone();
    let mut hash = Sha256::new();
    let mut part = |s: &str| -> io::Result<()> {
        hash.update((s.len() as u64).to_le_bytes());
        for chunk in s.as_bytes().chunks(64 * 1024) {
            remaining.cancellation.check().map_err(io::Error::other)?;
            if started.elapsed() >= remaining.timeout {
                return Err(io::Error::other(
                    "committed export deadline reached while hashing sources",
                ));
            }
            remaining.max_work = remaining.max_work.checked_sub(1).ok_or_else(|| {
                io::Error::other("committed export work limit reached while hashing sources")
            })?;
            hash.update(chunk);
        }
        Ok(())
    };
    part("root")?;
    part(&membership.root)?;
    for (root, info) in &membership.roots {
        part("member-root")?;
        part(root)?;
        for library in &info.libraries {
            part("library")?;
            part(library)?;
        }
        for file in &info.files {
            part("member-file")?;
            part(file)?;
        }
    }
    for source in sources {
        part("source")?;
        part(&source.uri)?;
        part(&source.text)?;
    }
    remaining.timeout = remaining.timeout.saturating_sub(started.elapsed());
    Ok((format!("sha256:{:x}", hash.finalize()), remaining))
}

struct Temporary(PathBuf);
impl Drop for Temporary {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.0);
    }
}

/// Link a complete sibling temporary file into place, atomically without
/// overwriting an existing artifact (including a concurrent writer's artifact).
pub fn publish<T>(
    path: &Path,
    limits: &denotate_ir_text::committed::ExportLimits,
    write: impl FnOnce(&mut BufWriter<File>) -> io::Result<T>,
) -> io::Result<T> {
    let started = std::time::Instant::now();
    if path.extension().is_none_or(|e| e != "den") {
        return Err(io::Error::other("--export-committed needs a new .den file"));
    }
    if path.try_exists()? {
        return Err(io::Error::new(
            io::ErrorKind::AlreadyExists,
            "export destination already exists",
        ));
    }
    static SERIAL: AtomicU64 = AtomicU64::new(0);
    let parent = path.parent().unwrap_or(Path::new("."));
    let temporary_path = parent.join(format!(
        ".denotate-export-{}-{}.tmp",
        std::process::id(),
        SERIAL.fetch_add(1, Ordering::Relaxed)
    ));
    let file = File::options()
        .write(true)
        .create_new(true)
        .open(&temporary_path)?;
    // Own cleanup only after create_new succeeds; an existing temp is not ours.
    let temporary = Temporary(temporary_path);
    let mut writer = BufWriter::new(file);
    let result = write(&mut writer)?;
    writer.flush()?;
    writer.get_ref().sync_all()?;
    limits.cancellation.check().map_err(io::Error::other)?;
    if started.elapsed() >= limits.timeout {
        return Err(io::Error::other(
            "committed export deadline reached before publication",
        ));
    }
    fs::hard_link(&temporary.0, path)?;
    Ok(result)
}
