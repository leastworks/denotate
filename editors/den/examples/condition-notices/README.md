# Contextual condition notices

Run `just check-den editors/den/examples/condition-notices` from the repository root,
or open this folder in the `.den` editor.

`outer` varies. Within `selected AND eligible`, `repeated` is always true and
`incompatible` is impossible. `suppressed` has an unreachable parent and stays quiet.
The two diagnostics are advisory, so the command succeeds. Add `--json` to see all
four results and their replayed worlds. No obligation is selected.
