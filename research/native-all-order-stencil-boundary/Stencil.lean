import GreenPairing
import Mathlib.Data.Nat.Choose.Sum

namespace CarryStencilBoundary
open CarrySelfAdjointOperator NativeLaguerre CarryNativeTfvd CarryCriticalTfvd
open CarryCurvatureGreen CarryLinearTfvd
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

/-- The EXISTING signed binomial weights, before factorial or radial scaling. -/
def rawStencil (m : ℕ) : ℕ →₀ ℂ :=
  ∑ j ∈ Finset.range (m+1), completedGreenForwardWeight m j • Finsupp.single j 1

/-- The static factorial normalization; radial phase is kept separately below. -/
def staticStencil (m : ℕ) : ℕ →₀ ℂ := (m.factorial : ℂ)⁻¹ • rawStencil m

/-- Literal coefficient input of projectiveChiralDifferenceJet, including its
original imaginary radial step. This is not defined from a desired Gram. -/
def radialJetCoefficients (k m : ℕ) : ℕ →₀ ℂ :=
  ((m.factorial : ℂ)*canonicalCompletedC3RadialSecondStep k^m)⁻¹ • rawStencil m

def radialLeadingScalar (k m : ℕ) : ℂ :=
  ((m.factorial : ℂ)*canonicalCompletedC3RadialSecondStep k^m)⁻¹ * (-1)^m

theorem raw_stencil_apply (m j : ℕ) : rawStencil m j=completedGreenForwardWeight m j := by
  classical
  simp only [rawStencil, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finsupp.smul_apply, smul_eq_mul]
  by_cases hj : j < m+1
  · rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hbj
      simp [Finsupp.single_eq_of_ne hbj.symm]
    · simp [hj]
  · rw [show completedGreenForwardWeight m j=0 by
      simp [completedGreenForwardWeight, Nat.choose_eq_zero_of_lt (by omega : m < j)]]
    apply Finset.sum_eq_zero
    intro b hb
    have hbj : b ≠ j := by have := Finset.mem_range.mp hb; omega
    simp [Finsupp.single_eq_of_ne hbj.symm]

theorem raw_stencil_zero (m : ℕ) : rawStencil m 0=(-1 : ℂ)^m := by
  rw [raw_stencil_apply]
  simp [completedGreenForwardWeight]

theorem raw_stencil_one (m : ℕ) : rawStencil m 1=-(m : ℂ)*(-1 : ℂ)^m := by
  rw [raw_stencil_apply]
  cases m with
  | zero => simp [completedGreenForwardWeight]
  | succ m =>
    simp only [completedGreenForwardWeight, Nat.add_sub_cancel, Nat.choose_one_right,
      Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
      Nat.cast_add, Nat.cast_one, pow_succ]
    push_cast
    ring

theorem radial_jet_two_traces (k m : ℕ) :
    radialJetCoefficients k m 0=radialLeadingScalar k m ∧
    radialJetCoefficients k m 1=-(m : ℂ)*radialLeadingScalar k m := by
  simp only [radialJetCoefficients, Finsupp.smul_apply, smul_eq_mul,
    raw_stencil_zero, raw_stencil_one, radialLeadingScalar]
  constructor
  · trivial
  · ring

/-- Exact whole-vector provenance in the original TWO completed channels. -/
theorem radial_jet_original_source (k m : ℕ) :
    physicalCompletedFiniteSource k (radialJetCoefficients k m)=
      projectiveChiralDifferenceJet k m := by
  rw [physicalCompletedFiniteSource_original]
  simp only [radialJetCoefficients, rawStencil, map_smul, map_sum,
    Finsupp.linearCombination_single, projectiveChiralDifferenceJet, one_smul]

theorem advance_power_feature (m : ℕ) :
    (physicalRadialAdvance^m) (completedNativeChiralCauchyFeature 0)=
      completedNativeChiralCauchyFeature m := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ', mul_apply_eq_comp, ih, physicalRadialAdvance_feature]

theorem negative_unit_power (m : ℕ) :
    (-1 : PhysicalSpace →L[ℂ] PhysicalSpace)^m=
      ((-1 : ℂ)^m) • (1 : PhysicalSpace →L[ℂ] PhysicalSpace) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, ih]
    have hn : (-1 : PhysicalSpace →L[ℂ] PhysicalSpace)=(-1 : ℂ) • 1 := by simp
    rw [hn, smul_mul_assoc, mul_smul_comm, one_mul, smul_smul, pow_succ]

theorem raw_stencil_binomial (m : ℕ) :
    physicalCauchySynthesis (rawStencil m)=
      ((physicalRadialAdvance-1)^m) (completedNativeChiralCauchyFeature 0) := by
  have hb := ((Commute.one_right physicalRadialAdvance).neg_right).add_pow m
  have hh := congrArg (fun T : PhysicalSpace →L[ℂ] PhysicalSpace =>
    T (completedNativeChiralCauchyFeature 0)) hb
  rw [sub_eq_add_neg, hh]
  simp only [rawStencil, map_sum, map_smul, physicalCauchySynthesis,
    Finsupp.linearCombination_single, sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  simp only [mul_apply_eq_comp, ContinuousLinearMap.natCast_apply, negative_unit_power,
    smul_apply, one_apply_eq_self, map_smul, advance_power_feature,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  congr 1
  simp only [completedGreenForwardWeight, Int.cast_mul, Int.cast_pow,
    Int.cast_neg, Int.cast_one, Int.cast_natCast]
  ring

/-- The binomial stencil is identified with the SAME physical complement. -/
theorem raw_stencil_complement (m : ℕ) :
    physicalCauchySynthesis (rawStencil m)=
      ((-1 : ℂ)^m) • ((physicalComplement^m) (completedNativeChiralCauchyFeature 0)) := by
  rw [raw_stencil_binomial]
  have hn : physicalRadialAdvance-1 = -physicalComplement := by
    unfold physicalComplement
    abel
  rw [hn, neg_pow, negative_unit_power, smul_mul_assoc, one_mul, smul_apply]

theorem radial_jet_synthesis (k m : ℕ) :
    physicalCauchySynthesis (radialJetCoefficients k m)=
      radialLeadingScalar k m • ((physicalComplement^m) (completedNativeChiralCauchyFeature 0)) := by
  simp only [radialJetCoefficients, map_smul, raw_stencil_complement, smul_smul,
    radialLeadingScalar]

theorem radial_leading_nonzero (k m : ℕ) : radialLeadingScalar k m ≠ 0 := by
  unfold radialLeadingScalar
  apply mul_ne_zero
  · exact inv_ne_zero (mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero m)
      (pow_ne_zero m (canonicalCompletedC3RadialSecondStep_ne_zero k)))
  · exact pow_ne_zero m (by norm_num)

end
end CarryStencilBoundary
