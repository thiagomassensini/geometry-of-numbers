# Theorem and dependency map

## Original sequence and target

```text
original C2 source
  → Genuine / native characteristic
  → completedNativeCharacteristicContinuation = F
  → C4 log response / completedSigmaLogJet H_n
  → CarrySigmaPade.sigmaPadeD 0 s = H_s H_(s+2) − H_(s+1)^2
```

`CarrySigmaPade.sigmaPadeD` is in `research/native-moving-schur-sigma/SigmaPadeCorrespondence.lean`, lines 21–24, namespace `CarrySigmaPade`. The formal source is not defined from zeros. `CarrySigmaSource.completedSigmaLogJet` is declared in `research/native-sixth-explicit-sigma/SigmaParity.lean`, lines 24 onward; its central response is tied to `completedNativeOperatorCharacteristic` in that module. `SigmaZeroObstruction.completedSigmaLogJet_quarter_normalization` and `completedSigmaLogJet_eq_logDisplacedProduct` expose the normalization and C4 log-derivative interpretation.

## Height-50 certificate and multiplicity

`research/native-moving-schur-sigma/SigmaRHHeightBridge.lean`:

- `sigmaRHStripZerosUpTo (T : ℝ) : Set ℂ` — zeta zeros with `0 < re < 1`, `0 < im ≤ T`.
- `sigmaRHHeight50 : Prop` — RH location and simple zeta zeros through height 50.
- `sigmaZeroCount50 : Prop` — `ncard = 10` of the above set (distinct points; multiplicity is supplied separately by simplicity).
- `sigmaTenZeroBoxLower/Upper : Fin 10 → ℝ` — rational ordinate interval endpoints.
- `sigmaTenZeroBoxesWithFirst (γ : ℝ) : Prop` — strictly monotone family of ten boxed line zeros with first ordinate fixed to γ.
- `sigmaTenZeroBoxesWithFirst_of_first_and_nine` combines the first bracket and nine remaining boxes.
- `sigmaLineZero_small_eq_first` uses the distinct count and ten disjoint boxes to show a small positive line zero equals the first boxed zero.
- `completedNativeCharacteristicContinuation_zero_iff_zeta` identifies zeros in the critical strip; `completedNativeCharacteristicContinuation_order_eq_zeta` transports analytic multiplicity; `sigmaContinuation_zero_order_one_of_height50` supplies simplicity for native continuation zeros within `|re| ≤ 50`.
- `exists_firstSigmaDisplacedProductIsolation_from_height50` currently packages a first-pole isolation theorem. It does not construct ten moments or a Hadamard tail.

`SigmaHeight50Integration.lean` imports `RHHeight.Main`, `HardyFirstZero.FirstZero`, and `HardyTenZeros.TenZeros`, proving private wrappers for RH, count, first zero, and nine additional boxes. The dependency footprint and `#print axioms` output must be checked in this Lean 4.32 worktree before using the certificates in a new theorem.

## Native continuation

`SigmaNativeContinuation.lean` defines `completedNativeCharacteristicContinuation (z : ℂ) : ℂ` from the regularized completed zeta and proves analyticity, evenness, and equality with the native characteristic on the genuine strip. This establishes an entire continuation but does **not** prove order ≤1 or a Hadamard product.

## Existing adjacent results

- `SigmaTwoPoleModel.lean`: finite algebra for a two-pole model only.
- `SigmaTransverseAllOrder.lean`: local-in-index transverse derivatives and Taylor data; does not supply the C2 ten-mode tail or a global uniform radius in the index.
- `SigmaRemainderDescent.lean`: a two-pole remainder under fixed-displacement isolation; not the all-order central ten-mode decomposition.
- `SigmaCurvature.lean` and `SigmaParity.lean` do not live under the sigma subdirectory in current `origin/main`; equivalent declarations exist in `research/native-sixth-explicit-sigma/`. No import names should be assumed without checking module paths.

## Compiled B1 conditional theorem

The four B1 modules compile under Lean 4.32 with `-DwarningAsError=true`:

1. `SigmaCentralTenModeAlgebra.lean` defines generic finite power sums and consecutive Hankel minors; it proves the Vandermonde-pair identity and the five-term determinant-error bound.
2. `SigmaCentralTenModeRationalGate.lean` proves the rational scale boxes, the four shallow-window margins using the refined `T_n`, and the global error ratio for `s≥4`.
3. `SigmaCentralTenModeSourceGate.lean` proves
   `CarrySigmaPade.sigmaPadeD_center_pos_of_conditional_ten_mode_tail`, whose conclusion is
   `∀ s, 0 < CarrySigmaPade.sigmaPadeD 0 s`. Its explicit premises are the decomposition of the original `completedSigmaLogJet 0 n` into ten finite power modes plus `e n`, all ten rational scale boxes, the global bound `|e n| ≤ 60 * eta^(n+1)`, low-index nonnegativity for `n≤5`, and the refined tail for indices 1 through 4.
4. `SigmaCentralTenModeAxiomAudit.lean` prints eight theorem closures. The fail-closed checker passes with exactly `{propext, Classical.choice, Quot.sound}` and no `sorryAx`, `sorry`, or `admit`.

The ten-mode sequence is only a comparison sequence. The theorem does not assert that the original
source satisfies the decomposition or any of the numerical tail/sign premises. No zeros-based
definition replaces the original `completedSigmaLogJet` or `sigmaPadeD`.
