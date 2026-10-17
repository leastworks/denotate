use lsp_types::{Position, TextDocumentContentChangeEvent};
use tree_sitter::{InputEdit, Parser, Point, Tree};

/// Each frontend supplies its generated grammar; no language policy lives here.
pub fn parser(language: tree_sitter::Language) -> Result<Parser, tree_sitter::LanguageError> {
    let mut parser = Parser::new();
    parser.set_language(&language)?;
    Ok(parser)
}

/// Source text is authoritative. Tree-sitter byte/point columns are NOT LSP
/// UTF-16 columns, and lone CR is also a line break in the editor protocol.
pub struct Document {
    pub text: String,
    pub version: i32,
    pub open: bool,
    pub tree: Tree,
    lines: Vec<usize>,
}

impl AsRef<Document> for Document {
    fn as_ref(&self) -> &Document {
        self
    }
}

impl Document {
    pub fn new(parser: &mut Parser, text: String, version: i32, open: bool) -> Self {
        let tree = parser.parse(&text, None).expect("uncancelled parse");
        Self::from_tree(text, version, open, tree)
    }

    fn from_tree(text: String, version: i32, open: bool, tree: Tree) -> Self {
        let mut lines = vec![0];
        let bytes = text.as_bytes();
        let mut i = 0;
        while i < bytes.len() {
            if bytes[i] == b'\r' {
                i += 1;
                if bytes.get(i) == Some(&b'\n') {
                    i += 1;
                }
                lines.push(i);
            } else if bytes[i] == b'\n' {
                i += 1;
                lines.push(i);
            } else {
                i += 1;
            }
        }
        Self {
            text,
            version,
            open,
            tree,
            lines,
        }
    }

    /// Apply the LSP sequence transactionally. Each range addresses the text
    /// after preceding changes. Tree-sitter points count LF rows and byte columns,
    /// unlike the editor's CR/CRLF-aware UTF-16 positions.
    pub fn changed(
        &self,
        parser: &mut Parser,
        changes: &[TextDocumentContentChangeEvent],
        version: i32,
    ) -> Result<Self, &'static str> {
        let mut next = Self::from_tree(self.text.clone(), version, self.open, self.tree.clone());
        let mut reuse = true;
        for change in changes {
            if let Some(range) = change.range {
                if range.start > range.end {
                    return Err("Reversed edit range");
                }
                let start = next.offset(range.start).ok_or("Invalid edit start")?;
                let end = next.offset(range.end).ok_or("Invalid edit end")?;
                if start > end {
                    return Err("Reversed edit range");
                }
                let start_position = point(&next.text, start);
                let old_end_position = point(&next.text, end);
                next.text.replace_range(start..end, &change.text);
                if reuse {
                    next.tree.edit(&InputEdit {
                        start_byte: start,
                        old_end_byte: end,
                        new_end_byte: start + change.text.len(),
                        start_position,
                        old_end_position,
                        new_end_position: point(&next.text, start + change.text.len()),
                    });
                }
            } else {
                next.text = change.text.clone();
                reuse = false; // Full replacements retain the frozen fresh-parse workload.
            }
            next = Self::from_tree(next.text, version, self.open, next.tree);
        }
        next.tree = parser
            .parse(&next.text, reuse.then_some(&next.tree))
            .ok_or("Parse cancelled")?;
        Ok(next)
    }

    pub fn position(&self, byte: usize) -> Position {
        let line = self.lines.partition_point(|start| *start <= byte) - 1;
        Position::new(
            line as u32,
            self.text[self.lines[line]..byte].encode_utf16().count() as u32,
        )
    }

    pub fn offset(&self, position: Position) -> Option<usize> {
        // LSP clamps positions past a line/document end. A UTF-16 position
        // inside a surrogate pair rounds down to that scalar's start, so edits
        // never split a UTF-8 character in the retained source.
        let Some(&start) = self.lines.get(position.line as usize) else {
            return Some(self.text.len());
        };
        let mut column = 0;
        for (byte, ch) in self.text[start..].char_indices() {
            if column == position.character {
                return Some(start + byte);
            }
            if ch == '\r' || ch == '\n' {
                return Some(start + byte);
            }
            column += ch.len_utf16() as u32;
            if column > position.character {
                return Some(start + byte);
            }
        }
        Some(self.text.len())
    }
}

fn point(text: &str, byte: usize) -> Point {
    let prefix = &text[..byte];
    Point::new(
        prefix.bytes().filter(|b| *b == b'\n').count(),
        prefix.rfind('\n').map_or(byte, |at| byte - at - 1),
    )
}
