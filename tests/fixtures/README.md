# Fixtures

The `.ndjson` exports are copied from Tenet's test fixtures (github.com/keithadler/tenet, `tests/fixtures`), which say how each was made:

| Export | Lean | Format |
|---|---|---|
| `Nat.add_succ.ndjson` | 4.34.0-rc2 | lean4export 3.1.0 |
| `Nat.add_succ.v3.0.ndjson` | 4.27.0-rc1 | lean4export 3.0.0 |
| `eta437.ndjson` | 4.37.0-rc1 | lean4export 3.1.0 |
| `acc436.ndjson` | 4.36.0 | lean4export 3.1.0 |

Each `.trace.ndjson` was made from the export beside it by Tenet's `trace-recall` branch (commit `8158d13`), which records checking-mode inference as `Check` and recalls earlier conclusions with `"of"`:

```bash
tenet check Nat.add_succ.ndjson --trace Nat.add_succ.trace.ndjson
```

Regenerate them when the trace format changes.
