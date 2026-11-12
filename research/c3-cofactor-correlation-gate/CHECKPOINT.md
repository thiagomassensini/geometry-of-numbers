# Checkpoint — correlated C3 coefficient gate

- Phase: finite odd third-block source certificate completed; final validation is reproducible.
- Branch: `agent/c3-cofactor-correlation-gate-20261112`; base `de8f044d78260fd4ba9f728c3bb313adfa0255df`.
- Latest prior commit: `a4116b7`; continuation commit: `8b4268a`.
- New Lean modules: `ChartReciprocal`, `BaseCoefficient`, `CompletedCoefficient`, `CorrelationInterval`, `LeftJetMagnitudeLow/High`, `LeftJetMagnitude`, `BoundaryTransport`, `FiniteReferenceTable`, `SourceCoefficientGreen`.
- Reused existing modules: `GammaHeadCrosswalk`, `C3CompletionTail48`, `GammaThirteen`, `IntervalGate`, `SourceGate`.
- Proven: shared-variable completed coefficient polynomial and outward-rounded interval containment.
- Proven: thirteen correlated left-jet absolute bounds sum to at most `1/2`.
- Proven: C3/48 tail jets through order 12 are at most `2e-24`; Gamma replacement is at most `0.5e-24`.
- Proven: original native `c_0,...,c_6` lie in the existing candidate coefficient balls.
- Proven: `completed_native_odd_third_block_posDef` via the existing source cofactor gate.
- Finite status: odd size-3 source block GREEN; even size-3 block and all-order positivity remain open.
- Validation command: `bash research/c3-cofactor-correlation-gate/validate.sh` (Lean 4.32.0, warnings as errors, Python exact-rational diagnostics, diff check).
- Validation passed: task script, `lake build --wfail` (8,850 jobs), and foundation/geometry/analysis audits.
- Axioms printed for final results: only `propext`, `Classical.choice`, and `Quot.sound`.
- Difficulties resolved: avoided expensive `range`-sum reduction by proving the finite magnitude sum with `Fin.sum_univ_succ`; included nested `.cache/pr37` import paths in the validator.
- No source scale, completion, phase, boundary, or tail was altered; no theta sign premise is used.
- Next exact action: inspect the complete diff, commit and push this checkpoint, then check PR status.
- Remaining obligation: independently certify the even-sector third-direction margin from the original C3 source; all-order sign remains separate.
