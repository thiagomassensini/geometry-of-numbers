# C3 shifted fourth block: resumed certificate status

## Objective and status

This work targets the shifted 4×4 Hankel block (`s = 1`, `n = 3`) from the original completed C3 source, using the M=80 C3/48 head, the original Gamma completion, and the existing M=80 tail ledger. Status is **PARTIAL**. The Lean development now transports the original source to correlated reference jets through order 16 and formally encloses those reference jets, but it does not prove the numeric inclusion needed for the fourth pivot.

The two third pivots proved in GoN #323/#324 are reused only as established prefix results. No theta/Stieltjes positivity is used to prove the fourth direction. No central 4×4 conclusion is claimed.

## Provenance

- Task worktree base: `6c5c97b03925c398bf77a561d6e76b14563265e0`; branch `agent/c3-shifted-fourth-certificate-20261112`.
- Toolchain: Lean 4.32.0; Mathlib pin `81a5d257c8e410db227a6665ed08f64fea08e997`; GreenFrame pin `cd2d838bee67ad23f869a02f8ed9f0a0feb926fa`.
- Source modules reused from `research/c3-cofactor-chiral-certification/` and `research/c3-cofactor-correlation-gate/`, including `C3CompletionTail48`, `GammaThirteen`, `GammaHeadCrosswalk`, `SourceCoefficientGreen`, `FiniteReferenceTable`, and the existing coefficient/moment identities.
- The original bracket, completion, M=80 cutoff, boundary stencil, and tail bound were not altered.

## Lean results

The new modules prove:

- `gamma_reference_center_difference13` and `native_gamma_crosswalk_boxes`: the rational Gamma reference is crosswalked to the old table and the native Gamma error is bounded through jet 16.
- `completed_head80_gamma_replacement_error_crosswalk` and `completed_native_jet_crosswalk_error80`: exact M=80 head/Gamma replacement and original tail transport, with the weighted per-jet Gamma allowance.
- `convolution_eq_realJetSeries_coeff`, `realJetSeries_convolution`, and `convolution_cross_through_sixteen`: exact convolution reindexing via formal power series.
- `finite_completed_crosswalk_eq_normalized80`: exact scale relation from the finite completed reference jets to the correlated normalized reference jets.
- `normalized_chart_reciprocal_box17_table_bound` and `normalized_chart_reciprocal_box17_table_contains`: rational table bounds for the normalized chart reciprocal through order 16, proved from its recurrence and the original chart boxes.
- `normalized_outer_base_polynomial_coefficient_box_verified17_contains`, `normalized_outer_completed_polynomial_box_verified17_contains`, and `normalized_completed_reference_box_verified80_contains`: formal interval containment for the correlated normalized completion reference through jet 16.
- `tight_high_sample_amplitude_evaluator_check`: each of the 60 new M=80 amplitude boxes for sample addresses 206–265 is checked by Lean against the original rational `expBox` calculation.
- `tight_high_sample_amplitude_contains`, `tight_high_sample_jet_box`, `cached_m80_sample_jet_box`, and `tight_head80_jet_box_cached`: enclosures for the additional high samples and the exact M=80 head, for every jet order. The first 205 sample amplitudes reuse the already certified primitive boxes.
- `native_coefficient_sourceJet_eq` and `native_jet_crosswalk_real_bound17`: identify the native completed coefficient with the original completed-source jet and bound its difference from the signed finite M=80 reference jet, using the original jet/Gamma/tail allowances.
- `native_finite_coefficient_box17_contains` and `native_coefficient_box17_contains`: prove containment of the signed finite reference coefficient and of the native coefficient in their computed Lean `Box` enclosures for indices 0 through 8. The latter boxes are the direct propagated boxes; they are not the tighter correlated candidate envelopes used by the numerical gate.
- `native_odd_fourth_block_eq`: expands the odd-sector 4×4 Bézout source block from its defining formal kernel, with the expected linear `−8 c₀c₈` term in the last diagonal. It is a matrix identity only; no determinant, Schur, or positivity theorem follows from it.

Direct compilation was done with `-DwarningAsError=true`. `Audit17.lean` reports only `[propext, Classical.choice, Quot.sound]` for the new theorem roots. The placeholder scan found no `sorry`, `admit`, `native_decide`, or new axioms.

## Numerical gate and what remains unproved

`preflight_correlated_coefficients.py` computes exact rational candidate boxes from the same-log-π correlated completion and the weighted Gamma/M=80 tail ledger. Its coefficient radii fit the chosen candidate radii through `c₈`; for the fixed rational Bézout direction, the 3,192-term exact interval expansion has lower bound

`6.74360518689508947997160988154063898922555 × 10⁻⁵⁴ > 0`.

That proves only that the **candidate boxes** pass the gate. It does not prove that the original native coefficients lie in those boxes. The independent-box diagnostic loses correlation and gives a lower bound about `−2.1772 × 10⁻⁴⁵`, so it cannot close the sign.

The direct Lean crosswalk and source-box containment are now formalized, but an attempted proof that the propagated nested `Box` enclosures are subsets of the tighter candidate envelopes was computationally impractical: unfolding the finite rational grid/convolution expressions spent 6m49s without closing the first containment. That attempt was removed rather than treating the diagnostic as a Lean proof. The resulting coefficient and block modules compile; candidate inclusion remains open.

The resumed work removes that head-evaluation bottleneck. `TightInputTable17.lean` caches the first 205 outputs of the original rational log and exponential box evaluators, and `TightInputCertificates17.lean` checks those values in Lean. The 60 high-address amplitudes continue to use the previously checked M=80 table. `GridArithmetic17.lean` and `GridHeadEvaluation17.lean` evaluate sample jets on an integer grid; the factorial reciprocal is applied as an exact rational scale before the final rounding, avoiding a large interval from rounding `1/r!` first. `GridJetCertificates17.lean` proves the resulting head intervals contain the original M=80 bracket jets:

- order 14: `[1950031647244927799/10^30, 1950031647244938748/10^30]`;
- order 16: `[590644054642505800/10^30, 590644054642507801/10^30]`.

The rational generator reproduces the caches, and Lean checks all 530 sample-jet entries before using them in the head sum. This is a Lean containment for the original finite M=80 head, not yet an inclusion for the completed native coefficients `c₇,c₈`.

Consequently, the shifted 4×4 Bézout determinant, its Schur complement, `0 < sourceMomentSchur h 1 3`, and `PosDef (G₁,4)` remain **unproved**. The existing third-prefix positivity does not supply the missing fourth margin by itself.

## Validation and audit notes

- In this continuation, the first candidate-subset reduction was interrupted after 6m49s without closing. After removing that unproved, computationally impractical theorem, the final `bash research/c3-shifted-fourth-certificate/validate.sh` passed end to end: all Lean modules with `-DwarningAsError=true`, `Audit17.lean`, both table regenerators, both rational preflights, placeholder scan, and `git diff --check`.
- The updated `Audit17.lean` reports only `[propext, Classical.choice, Quot.sound]` for the new source-box and 4×4 identity theorems. Python preflights passed: the candidate-box gate lower bound remains `6.743605186895089… × 10⁻⁵⁴ > 0`, while the independent-box control remains negative. The correlated result is still diagnostic until native `c₇,c₈` are proved to lie in the candidate boxes.
- `research/c3-cofactor-correlation-gate/validate.sh`: passed, including its existing source coefficient and tail checks.
- The legacy `research/c3-cofactor-chiral-certification/validate.sh` stopped at `ChiralOrder11` because its `LEAN_PATH` omitted the existing `CompletedHeadEight.olean` dependency. After adding that dependency cache locally (without editing the validator or dependency source), the remaining #324 modules, `SourceSchurShift`, and certificate audit compiled. The certificate audit reports 17 result roots and excludes the alternative sign routes.
- Diagnostics `diagnose_completed_boxes48.py` and `compare_c3_heads.py` ran; the former's old independently boxed cofactor interval contains zero, as expected from lost correlation.
- `lake build --wfail` passed in the legacy dependency worktree (`cf66116e72a19b27be5441cda34e1fb723b88adc`, 8,850 jobs). `audit-foundation.sh`, `audit-geometry.sh`, and `audit-analysis.sh` all passed there.
- The root build and audits do not compile the new `research/` modules; those were compiled directly by the task validator.
- Whitespace and placeholder scans passed. Checkpoint commit `fc35ebd` contains only this task's research artifacts; the branch is kept separate and has not been merged. The main GoN and Carry checkouts contain unrelated pre-existing changes that were left untouched.

## Next exact obligation

Replace the slow unfolding of the nested rational `Box` sums with compact exact endpoint certificates and prove native `c₇,c₈` inclusion in the correlated candidate boxes. Only after those inclusions are proved can the fixed-direction gate or an exact determinant/Schur certificate conclude the shifted fourth pivot.
