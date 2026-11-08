# B1 Lean 4.32 build and axiom audit

The B1 builds ran on `9d45f4e03b3e40186c74e72dba5e8077ecc59f8d`. After the C5 loop exited,
`origin/main` advanced through C5-only commits; the branch fast-forwarded to
`ebd6c57c33edcf8596f09889c7bf956e7d9b284f`. The intervening diff contains only C5 files, and the
C2 import sources used by these builds were rechecked byte-for-byte against the integration
worktree afterward. Lean toolchain: `leanprover/lean4:v4.32.0`; every compile used
`-DwarningAsError=true` through
`compile_sigma_pade.sh`, with the exclusive output directory
`/home/thlinux/tmp/c2-central-hankel2-20261107-lean432`.

All four modules compiled with exit status 0:

| Module | Result | `.olean` SHA256 |
|---|---:|---|
| `SigmaCentralTenModeAlgebra` | pass | `f123f2e038a6a2b66100fdb23c7c8a50900b325ae6c36d6a82f3e6cfbfa5b1c7` |
| `SigmaCentralTenModeRationalGate` | pass | `d6cc841481c2fd155c22f2b49a745137f6406c826236a469b0d83421faac9fa3` |
| `SigmaCentralTenModeSourceGate` | pass | `4224c9c62370f6190fb8edcb6b7de7b74cab3d448a3289e9875f85ff4e1c03c3` |
| `SigmaCentralTenModeAxiomAudit` | pass | `418980da1136df7acb55b09328d4a514d7376c0278dd1bfc2134f9376bf9e8c7` |

The two original-source modules used the read-only, hash-matched C2 integration cache and the
read-only Geometry of Numbers library build containing `CanonicalFiniteHeight`. That source is
tracked at commit `d1577400c0d61bc90ecfd1f5759b8e4aaf5fc241`. The C2 import sources were rechecked
byte-for-byte against the cache worktree after fast-forwarding `origin/main` to `ebd6c57`.

The captured Lean output is in this directory. The three successful compile logs are empty because
Lean emitted no diagnostics; the audit log contains all eight `#print axioms` reports. The
fail-closed checker exited 0 and reports exactly the allowed standard axioms for every theorem:
`propext`, `Classical.choice`, and `Quot.sound`. It rejects any extra axiom, `sorryAx`, `sorry`, or
`admit`. Source and `.olean` hashes are in `SOURCE_HASHES_B1.sha256` and `OLEAN_HASHES_B1.sha256`.

This build proves the conditional theorem over explicit ten-mode, box, global-tail, low-index-sign,
and refined-tail premises. It does not prove those premises from the native continuation, so it is
not the unconditional all-window result.
