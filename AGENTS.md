## Lean verification

- For Lean files, use `lean-lsp-mcp` by default.
- After edits, use `lean_diagnostic_messages`.
- Use `lean_goal` and `lean_multi_attempt` while developing proofs.
- Use `lean_build` only when imports change or the LSP needs refreshing.
- Do not run `lake env lean <file>` unless LSP diagnostics are unavailable or inconclusive.
