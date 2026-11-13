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

Direct compilation was done with `-DwarningAsError=true`. `Audit17.lean` reports only `[propext, Classical.choice, Quot.sound]` for the new theorem roots. The placeholder scan found no `sorry`, `admit`, `native_decide`, or new axioms.

## Numerical gate and what remains unproved

`preflight_correlated_coefficients.py` computes exact rational candidate boxes from the same-log-π correlated completion and the weighted Gamma/M=80 tail ledger. For the fixed rational Bézout direction, the 3,192-term exact interval expansion has lower bound

`6.74360518689508947997160988154063898922555 × 10⁻⁵⁴ > 0`.

That proves only that the **candidate boxes** pass the gate. It does not prove that the original native coefficients lie in those boxes. The independent-box diagnostic loses correlation and gives a lower bound about `−2.1772 × 10⁻⁴⁵`, so it cannot close the sign.

The new chart table removes recursive chart-reciprocal expansion. The resume added exact rational amplitudes for the 60 extra M=80 samples and a cached Lean head enclosure. The remaining bottleneck is numeric evaluation: Lean evaluation of the cached M=80 head jet 14, and even of one cached sample jet, reached about 8.54 GB without finishing within 3½ minutes. I stopped those exploratory reductions. A Python exact-rational diagnostic gives approximate tight-head intervals `[1.9500316472449276e-12, 1.9500316472449389e-12]` for jet 14 and `[5.9064405464250576e-13, 5.9064405464250778e-13]` for jet 16. These diagnostics use tighter low-address boxes than the cached Lean head and are not proof of its interval inclusion. The table generator `generate_high_amplitudes.py` reproduces the 60 amplitude entries exactly, while Lean independently checks each entry against `expBox`. There is still no Lean proof that the head jets 14 and 16, after completion and tail transport, lie in the candidate coefficient boxes for `c₇` and `c₈`.

Consequently, the shifted 4×4 Bézout determinant, its Schur complement, `0 < sourceMomentSchur h 1 3`, and `PosDef (G₁,4)` remain **unproved**. The existing third-prefix positivity does not supply the missing fourth margin by itself.

## Validation and audit notes

- `bash research/c3-shifted-fourth-certificate/validate.sh`: passed after the resume additions. It explicitly compiled all task Lean modules with warnings as errors, audited all new public theorem roots, checked the generated high-amplitude table, scanned for forbidden placeholders/axioms, and ran the two exact-rational diagnostics.
- `research/c3-cofactor-correlation-gate/validate.sh`: passed, including its existing source coefficient and tail checks.
- The legacy `research/c3-cofactor-chiral-certification/validate.sh` stopped at `ChiralOrder11` because its `LEAN_PATH` omitted the existing `CompletedHeadEight.olean` dependency. After adding that dependency cache locally (without editing the validator or dependency source), the remaining #324 modules, `SourceSchurShift`, and certificate audit compiled. The certificate audit reports 17 result roots and excludes the alternative sign routes.
- Diagnostics `diagnose_completed_boxes48.py` and `compare_c3_heads.py` ran; the former's old independently boxed cofactor interval contains zero, as expected from lost correlation.
- `lake build --wfail` passed in the legacy dependency worktree (`cf66116e72a19b27be5441cda34e1fb723b88adc`, 8,850 jobs). `audit-foundation.sh`, `audit-geometry.sh`, and `audit-analysis.sh` all passed there.
- The root build and audits do not compile the new `research/` modules; those were compiled directly by the task validator.
- Whitespace and placeholder scans passed. Checkpoint commit `fc35ebd` contains only this task's research artifacts; the branch is kept separate and has not been merged. The main GoN and Carry checkouts contain unrelated pre-existing changes that were left untouched.

## Next exact obligation

Prove correlated rational enclosures for the original M=80 head jets 14 and 16 without evaluating the whole repeated interval expression at once. Then use the already formalized weighted Gamma and original tail ledgers to prove the native `c₇,c₈` inclusions in the gate boxes. Only after that inclusion is proved can the existing cofactor identity and certified 3×3 prefix be used to conclude the shifted fourth pivot.
