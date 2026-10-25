import SchurBound
import CPFormal.Analytic.CpNativeGpreTowerNorm

namespace CarryVerticalSynthesis
open CarrySelfAdjointOperator CPFormal.Analytic.Cp
open scoped BigOperators InnerProductSpace lp ENNReal ComplexConjugate
open Filter Topology
noncomputable section
set_option autoImplicit false

/-- The original native real tower, with its original norm. -/
def finiteTower : (ℕ →₀ ℝ) →ₗ[ℝ] NativeGpreTowerHilbert :=
  Finsupp.linearCombination ℝ (fun j => lp.single 2 j (1 : ℝ))

/-- Literal finite source synthesis; no Gram-dependent coefficients. -/
def finiteSource : (ℕ →₀ ℝ) →ₗ[ℝ] CanonicalCompletedNativeChiralCauchyCarrier :=
  Finsupp.linearCombination ℝ completedNativeChiralCauchyFeature

theorem finite_tower_apply (c : ℕ →₀ ℝ) (i : ℕ) : finiteTower c i = c i := by
  classical
  change (∑ j ∈ c.support, c j • lp.single 2 j (1 : ℝ)) i = c i
  rw [lp.coeFn_sum]
  simp [lp.coeFn_smul, Finset.sum_apply, Pi.smul_apply, lp.single_apply, Pi.single_apply]
  exact fun h => h.symm

theorem finite_tower_norm_sq (c : ℕ →₀ ℝ) :
    ‖finiteTower c‖ ^ 2 = ∑ j ∈ c.support, (c j) ^ 2 := by
  have h := lp.norm_sum_single (p := 2) (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    (fun j => c j) c.support
  simpa [finiteTower, Finsupp.linearCombination_apply, Finsupp.sum,
    ← lp.single_smul, Real.rpow_two, Real.norm_eq_abs, sq_abs] using h

theorem finite_source_pairing (c d : ℕ →₀ ℝ) :
    inner ℂ (finiteSource c) (finiteSource d) =
      ((∑ i ∈ c.support, ∑ j ∈ d.support,
        c i * d j * (((i + j + 2 : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) := by
  classical
  simp only [finiteSource, Finsupp.linearCombination_apply, Finsupp.sum,
    sum_inner, inner_sum, inner_smul_left_eq_smul, inner_smul_right_eq_smul,
    RCLike.real_smul_eq_coe_mul, Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  rw [inner_completedNativeChiralCauchyFeature]
  simp only [RCLike.ofReal_eq_complex_ofReal]
  push_cast
  ring

theorem finite_source_bound (c : ℕ →₀ ℝ) :
    ‖finiteSource c‖ ≤ 2 * ‖finiteTower c‖ := by
  have h := cauchy_quadratic_bound c.support c
  have he : ‖finiteSource c‖ ^ 2 =
      ∑ i ∈ c.support, ∑ j ∈ c.support,
        c i * c j * (((i + j + 2 : ℕ) : ℝ))⁻¹ := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), finite_source_pairing]
    rfl
  rw [← he, ← finite_tower_norm_sq] at h
  nlinarith [norm_nonneg (finiteSource c), norm_nonneg (finiteTower c)]

theorem finite_tower_dense : DenseRange finiteTower := by
  intro X
  have h := lp.hasSum_single (p := (2 : ℝ≥0∞)) (by norm_num) X
  apply isClosed_closure.mem_of_tendsto h
  filter_upwards [] with s
  apply subset_closure
  refine ⟨∑ j ∈ s, Finsupp.single j (X j), ?_⟩
  simp only [map_sum, finiteTower, Finsupp.linearCombination_single]
  apply Finset.sum_congr rfl; intro j _
  rw [← lp.single_smul, smul_eq_mul, mul_one]

/-- Forward synthesis extended in the native tower topology, not an inverse. -/
def nativeSynthesis : NativeGpreTowerHilbert →L[ℝ]
    CanonicalCompletedNativeChiralCauchyCarrier :=
  finiteSource.extendOfNorm finiteTower

theorem native_synthesis_finite (c : ℕ →₀ ℝ) :
    nativeSynthesis (finiteTower c) = finiteSource c :=
  LinearMap.extendOfNorm_eq finite_tower_dense ⟨2, finite_source_bound⟩ c

theorem native_synthesis_bound (X : NativeGpreTowerHilbert) :
    ‖nativeSynthesis X‖ ≤ 2 * ‖X‖ :=
  LinearMap.norm_extendOfNorm_apply_le finite_tower_dense 2 finite_source_bound X

theorem native_synthesis_opNorm : ‖nativeSynthesis‖ ≤ 2 :=
  LinearMap.opNorm_extendOfNorm_le finite_tower_dense (by norm_num) finite_source_bound

theorem native_synthesis_column (j : ℕ) :
    nativeSynthesis (lp.single 2 j (1 : ℝ)) = completedNativeChiralCauchyFeature j := by
  simpa [finiteTower, finiteSource] using native_synthesis_finite (Finsupp.single j 1)

/-- Convergence occurs in the original physical carrier, before scalar readout. -/
theorem native_synthesis_hasSum (X : NativeGpreTowerHilbert) :
    HasSum (fun j => (X j) • completedNativeChiralCauchyFeature j) (nativeSynthesis X) := by
  have h := (lp.hasSum_single (p := (2 : ℝ≥0∞)) (by norm_num) X).map
    nativeSynthesis.toLinearMap.toAddMonoidHom nativeSynthesis.continuous
  apply h.congr_fun
  intro j
  change (X j) • completedNativeChiralCauchyFeature j = nativeSynthesis (lp.single 2 j (X j))
  have hs : (lp.single 2 j (X j) : NativeGpreTowerHilbert) =
      (X j) • lp.single 2 j (1 : ℝ) := by
    rw [← lp.single_smul, smul_eq_mul, mul_one]
  rw [hs, map_smul, native_synthesis_column]

theorem native_synthesis_unique
    (T : NativeGpreTowerHilbert →L[ℝ] CanonicalCompletedNativeChiralCauchyCarrier)
    (hT : ∀ j, T (lp.single 2 j (1 : ℝ)) = completedNativeChiralCauchyFeature j) :
    T = nativeSynthesis := by
  apply ContinuousLinearMap.ext; intro X
  have hc : IsClosed {Y : NativeGpreTowerHilbert | T Y = nativeSynthesis Y} :=
    isClosed_eq T.continuous nativeSynthesis.continuous
  refine finite_tower_dense.induction_on X hc ?_
  intro c
  rw [native_synthesis_finite]
  simp only [finiteTower, finiteSource, Finsupp.linearCombination_apply, Finsupp.sum,
    map_sum, map_smul, hT]

/-- The extension stays in the closure of the ORIGINAL physical columns. -/
theorem native_synthesis_mem_original_closure (X : NativeGpreTowerHilbert) :
    nativeSynthesis X ∈ NativeLaguerre.physicalCauchyClosure := by
  let P := NativeLaguerre.physicalCauchyClosure.restrictScalars ℝ
  have hc : IsClosed {Y : NativeGpreTowerHilbert | nativeSynthesis Y ∈ P} :=
    NativeLaguerre.physicalCauchySpan.isClosed_topologicalClosure.preimage
      nativeSynthesis.continuous
  refine finite_tower_dense.induction_on X hc ?_
  intro c
  rw [native_synthesis_finite]
  classical
  change (∑ j ∈ c.support, c j • completedNativeChiralCauchyFeature j) ∈ P
  apply P.sum_mem
  intro j _
  apply P.smul_mem
  change completedNativeChiralCauchyFeature j ∈ NativeLaguerre.physicalCauchyClosure
  simpa only [NativeLaguerre.physicalCauchyFeature_coe] using
    (NativeLaguerre.physicalCauchyFeature j).property

end
end CarryVerticalSynthesis
