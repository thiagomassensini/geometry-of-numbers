import NativeSynthesis
import CarrySelfAdjointOperator.RealQuadratureDomainTransport

namespace CarryVerticalSynthesis
open CarrySelfAdjointOperator CPFormal.Analytic.Cp
open scoped BigOperators InnerProductSpace lp ENNReal ComplexConjugate
open Filter Topology
noncomputable section
set_option autoImplicit false

theorem native_synthesis_inner_im (X Y : NativeGpreTowerHilbert) :
    (inner ℂ (nativeSynthesis X) (nativeSynthesis Y)).im = 0 := by
  have hc : IsClosed {Z : NativeGpreTowerHilbert |
      (inner ℂ (nativeSynthesis Z) (nativeSynthesis Y)).im = 0} :=
    isClosed_eq (by fun_prop) continuous_const
  refine finite_tower_dense.induction_on X hc ?_
  intro c
  have hd : IsClosed {Z : NativeGpreTowerHilbert |
      (inner ℂ (nativeSynthesis (finiteTower c)) (nativeSynthesis Z)).im = 0} :=
    isClosed_eq (by fun_prop) continuous_const
  refine finite_tower_dense.induction_on Y hd ?_
  intro d
  rw [native_synthesis_finite, native_synthesis_finite, finite_source_pairing]
  rfl

/-- Both independent real quadratures are synthesized before complex packaging. -/
def quadratureSynthesis : RealQuadrature.Space NativeGpreTowerHilbert →L[ℝ]
    CanonicalCompletedNativeChiralCauchyCarrier :=
  nativeSynthesis.comp (WithLp.fstL 2 ℝ _ _) +
    (Complex.I • nativeSynthesis).comp (WithLp.sndL 2 ℝ _ _)

theorem quadrature_synthesis_apply (X : RealQuadrature.Space NativeGpreTowerHilbert) :
    quadratureSynthesis X = nativeSynthesis X.fst + Complex.I • nativeSynthesis X.snd := rfl

theorem quadrature_synthesis_norm_sq (X : RealQuadrature.Space NativeGpreTowerHilbert) :
    ‖quadratureSynthesis X‖ ^ 2 =
      ‖nativeSynthesis X.fst‖ ^ 2 + ‖nativeSynthesis X.snd‖ ^ 2 := by
  rw [quadrature_synthesis_apply, norm_add_sq (𝕜 := ℂ), inner_smul_right, norm_smul,
    Complex.norm_I, one_mul]
  simp [native_synthesis_inner_im]

theorem quadrature_synthesis_bound (X : RealQuadrature.Space NativeGpreTowerHilbert) :
    ‖quadratureSynthesis X‖ ≤ 2 * ‖X‖ := by
  have hX := native_synthesis_bound X.fst
  have hY := native_synthesis_bound X.snd
  have hXs := sq_le_sq₀ (norm_nonneg (nativeSynthesis X.fst))
    (by positivity : 0 ≤ 2 * ‖X.fst‖)
  have hYs := sq_le_sq₀ (norm_nonneg (nativeSynthesis X.snd))
    (by positivity : 0 ≤ 2 * ‖X.snd‖)
  have hN := WithLp.prod_norm_sq_eq_of_L2 X
  have hQ := quadrature_synthesis_norm_sq X
  nlinarith [(hXs.mpr hX), (hYs.mpr hY), norm_nonneg (quadratureSynthesis X), norm_nonneg X]

theorem quadrature_synthesis_hasSum (X : RealQuadrature.Space NativeGpreTowerHilbert) :
    HasSum (fun j => ((X.fst j : ℂ) + Complex.I * (X.snd j : ℂ)) •
      completedNativeChiralCauchyFeature j) (quadratureSynthesis X) := by
  have h := (native_synthesis_hasSum X.fst).add
    ((native_synthesis_hasSum X.snd).const_smul Complex.I)
  rw [quadrature_synthesis_apply]
  apply h.congr_fun
  intro j
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ),
    RCLike.ofReal_eq_complex_ofReal, smul_smul, add_smul]

/-- All four ordered quadrature crossings are retained on independent states. -/
theorem quadrature_synthesis_pairing
    (X Y : RealQuadrature.Space NativeGpreTowerHilbert) :
    inner ℂ (quadratureSynthesis X) (quadratureSynthesis Y) =
      inner ℂ (nativeSynthesis X.fst) (nativeSynthesis Y.fst) +
      inner ℂ (nativeSynthesis X.snd) (nativeSynthesis Y.snd) +
      Complex.I * (inner ℂ (nativeSynthesis X.fst) (nativeSynthesis Y.snd) -
        inner ℂ (nativeSynthesis X.snd) (nativeSynthesis Y.fst)) := by
  simp only [quadrature_synthesis_apply, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, Complex.conj_I]
  have hi : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination
    - inner ℂ (nativeSynthesis X.snd) (nativeSynthesis Y.snd) * hi

theorem quadrature_synthesis_J (X : RealQuadrature.Space NativeGpreTowerHilbert) :
    quadratureSynthesis (RealQuadrature.J X) = Complex.I • quadratureSynthesis X := by
  simp only [quadrature_synthesis_apply, RealQuadrature.J_fst, RealQuadrature.J_snd,
    map_neg, smul_add, smul_smul, Complex.I_mul_I, neg_one_smul]
  abel

/-- Literal finite complex source coefficients; both quadratures keep level zero. -/
def finiteQuadratures {N : ℕ} (c : Fin N → ℂ) : RealQuadrature.Space NativeGpreTowerHilbert :=
  WithLp.toLp 2
    ((∑ j, (c j).re • lp.single 2 j.val (1 : ℝ) : NativeGpreTowerHilbert),
      (∑ j, (c j).im • lp.single 2 j.val (1 : ℝ) : NativeGpreTowerHilbert))

theorem finite_quadratures_fst {N : ℕ} (c : Fin N → ℂ) :
    (finiteQuadratures c).fst = ∑ j, (c j).re • lp.single 2 j.val (1 : ℝ) := rfl

theorem finite_quadratures_snd {N : ℕ} (c : Fin N → ℂ) :
    (finiteQuadratures c).snd = ∑ j, (c j).im • lp.single 2 j.val (1 : ℝ) := rfl

set_option maxHeartbeats 800000 in
theorem quadrature_synthesis_finite {N : ℕ} (c : Fin N → ℂ) :
    quadratureSynthesis (finiteQuadratures c) =
      ∑ j, c j • completedNativeChiralCauchyFeature j.val := by
  rw [quadrature_synthesis_apply, finite_quadratures_fst, finite_quadratures_snd]
  simp only [map_sum, map_smul, native_synthesis_column,
    Finset.smul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro j _
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ),
    RCLike.ofReal_eq_complex_ofReal, smul_smul, ← add_smul]
  congr 1
  simpa only [mul_comm] using Complex.re_add_im (c j)

/-- No independent finite coefficient direction disappears in this synthesis. -/
theorem finite_quadrature_synthesis_injective (N : ℕ) :
    Function.Injective (fun c : Fin N → ℂ => quadratureSynthesis (finiteQuadratures c)) := by
  intro c d h
  apply ChiralReturn.radialIncidentSynthesis_injective 0 N
  simpa [quadrature_synthesis_finite, ChiralReturn.radialIncidentSynthesis,
    completedNativeRadialChiralCauchyState] using h

end
end CarryVerticalSynthesis
