# Shared `.den` fixtures

Each directory containing `.den` files is a separate workspace for editor tests. Tests
copy one workspace, never this whole tree, so deliberately broken files do not leak
into other cases. Every workspace has a `den.root`; `base/00-valid/` is the standard
two-file example.

`syntax.json` records whole-file **syntax** acceptance per case (`base` and `extended`
profiles), checked by the `.den` server's component tests. `accept` means no parser
errors or recovery; it says nothing about resolution or typing (unknown sorts,
missing namespaces and ambiguous names deliberately parse).

The root `.gitattributes` disables text normalization for these files: some contain
deliberate CR and BOM bytes.

| Workspace | Purpose |
| --- | --- |
| `base/00-valid` | Library and program, without contracts |
| `base/01-missing-semicolon`, `02-unclosed-paren`, `03-truncated-argument` | Recovery from incomplete syntax |
| `base/04-unknown-sort`, `05-broken-import`, `06-broken-library-declaration` | Syntax-valid resolution failures; intact declarations survive |
| `base/07-ambiguous-import` | Two visible relations with the same name and distinct identities |
| `base/08-singleton-variable` | Singleton-variable lint |
| `base/09-formatting-recovery` | Stray punctuation, unknown characters, comments, Unicode |
| `base/10-typed-constants` | One spelling denotes different constants by expected sort |
| `base/11-input-definitions` | Facts and rule heads illegally defining an input |
| `base/12-direct-imports` | `use` is not transitive |
| `base/13-duplicates` | Duplicate constants and relations |
| `base/14-lexical-boundaries` | Case sensitivity, keyword prefixes, quoting |
| `base/15-rename-unrelated` | A same-spelled unrelated relation must not be renamed |
| `base/16-variable-binding` | Rule-local identity, fresh wildcards, unsafe variables |
| `base/17-lone-cr`, `base/18-leading-bom` | Byte-sensitive line ending and BOM handling |
| `extensions/zero-arity/*` | Zero-arity relations, wrong arity, missing parentheses |
| `ir-text/*` | Full-format cases: standalone files, export layout |
| `rejected/*` | Constructs outside the original base profile; several (contracts, integers, qualified names, files without a header) are valid in today's full grammar, as the syntax tests record |
