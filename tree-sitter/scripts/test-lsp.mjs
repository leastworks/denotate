import { spawnSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';
const root = fileURLToPath(new URL('../../', import.meta.url));
const server = fileURLToPath(new URL(`../dist/denotate-lsp${process.platform === 'win32' ? '.exe' : ''}`, import.meta.url));
const env = { ...process.env, DENOTATE_BACKEND: 'tree-sitter', DENOTATE_LSP_COMMAND: server, DENOTATE_LSP_ARGS: '[]' };
// Explicit B1/B2 subset: never count absent editor capabilities as passes.
for (const [binary, filter] of [
    ['b1'], ['b2'], ['editor', 'unopened_bom_file_uses_editor_columns'],
    ['editor', 'standalone_unicode_comment_shifts_outline_lines'],
    ['editor', 'damaged_library_does_not_prevent_importer_syntax_outline'],
    ['resolution', 'ambiguous_imports_never_choose_by_import_order_or_local_shadowing'],
    ['resolution', 'imports_are_direct_and_signatures_keep_their_declaring_sort_identity'],
    ['resolution', 'unknown_imports_module_mismatches_and_duplicate_declarations_are_diagnosed'],
    ['resolution', 'intact_library_declarations_still_resolve_with_a_broken_signature'],
    ['resolution', 'damaged_signatures_do_not_invent_arity_or_argument_type_errors'],
    ['resolution', 'native_completion_offers_visible_relations_and_typed_constants'],
    ['a2', 'native_relation_queries_reuse_semantics_and_refresh_source_ranges'],
    ['a2', 'parameter_sort_changes_constant_targets_and_completion_but_not_visibility'],
    ['acceptance', 'insertion_and_reordering_keep_answers_current_and_report_query_reruns']
]) {
    const result = spawnSync('cargo', ['test', '--manifest-path', `${root}Cargo.toml`, '--locked',
        '-p', 'denotate-lsp-tests', '--test', binary, ...(filter ? [filter] : []), '--', '--nocapture'], { env, stdio: 'inherit' });
    if (result.error) throw result.error;
    if (result.status !== 0) process.exit(result.status ?? 1);
}
