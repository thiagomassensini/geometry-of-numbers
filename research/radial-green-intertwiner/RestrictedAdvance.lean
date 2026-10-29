import RadialRefinement
import CarrySelfAdjointOperator.NativePhysicalGreenResolvent

/-! Restriction of the OLD multiplication operator to the OLD physical closure.
No operator is defined from moments or from the desired spectrum. -/
namespace CarryRadialGreen
open CarryPhysicalTrace CarryRadialRefinement CarrySelfAdjointOperator
open CarrySelfAdjointOperator.NativeLaguerre
open scoped BigOperators ComplexConjugate InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem physical_feature_zero_ne_zero : physicalCauchyFeature 0 ≠ 0 := by
  intro h
  have hn := physical_column_norm_sq 0
  rw [h,norm_zero] at hn
  norm_num at hn

instance physicalSpaceNontrivial : Nontrivial PhysicalCauchySpace :=
  ⟨⟨physicalCauchyFeature 0,0,physical_feature_zero_ne_zero⟩⟩

theorem advance_preserves_closure (x : PhysicalCauchySpace) :
    physicalRadialAdvance (x : CanonicalCompletedNativeChiralCauchyCarrier) ∈ physicalCauchyClosure := by
  refine physicalCauchyEmbedding_dense.induction_on x
    ((physicalCauchySpan.isClosed_topologicalClosure).preimage
      (physicalRadialAdvance.continuous.comp continuous_subtype_val)) ?_
  intro c
  change physicalRadialAdvance (physicalCauchySynthesis c) ∈ physicalCauchyClosure
  simp only [physicalCauchySynthesis,Finsupp.linearCombination_apply,Finsupp.sum,map_sum,map_smul,
    physicalRadialAdvance_feature]
  apply physicalCauchyClosure.sum_mem
  intro j _
  exact physicalCauchyClosure.smul_mem _ (by
    simpa only [physicalCauchyFeature_coe] using (physicalCauchyFeature (j+1)).property)

/-- Only a codomain/domain restriction of the pre-existing M_x. -/
def nativeAdvance : PhysicalCauchySpace →L[ℂ] PhysicalCauchySpace :=
  (physicalRadialAdvance.comp physicalCauchyClosure.subtypeL).codRestrict physicalCauchyClosure
    advance_preserves_closure

theorem native_advance_coe (x : PhysicalCauchySpace) :
    (nativeAdvance x : CanonicalCompletedNativeChiralCauchyCarrier) = physicalRadialAdvance x := rfl

theorem native_advance_feature (j : ℕ) :
    nativeAdvance (physicalCauchyFeature j) = physicalCauchyFeature (j+1) := by
  apply Subtype.ext
  simp only [native_advance_coe,physicalCauchyFeature_coe,physicalRadialAdvance_feature]

theorem native_advance_pow_feature (n j : ℕ) :
    (nativeAdvance^n) (physicalCauchyFeature j) = physicalCauchyFeature (j+n) := by
  induction n generalizing j with
  | zero => simp
  | succ n ih =>
    rw [pow_succ,mul_apply_eq_comp,native_advance_feature,ih]
    congr 1
    omega

theorem native_advance_norm_le_one : ‖nativeAdvance‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound nativeAdvance (by norm_num : (0 : ℝ) ≤ 1)
  intro x
  change ‖physicalRadialAdvance (x : CanonicalCompletedNativeChiralCauchyCarrier)‖ ≤ 1*‖x‖
  exact (physicalRadialAdvance.le_opNorm x).trans
    (mul_le_mul_of_nonneg_right physicalRadialAdvance_norm_le_one (norm_nonneg _))

theorem native_advance_isPositive : nativeAdvance.IsPositive := by
  refine ⟨?_,?_⟩
  · intro x y
    change inner ℂ (physicalRadialAdvance (x : CanonicalCompletedNativeChiralCauchyCarrier))
      (y : CanonicalCompletedNativeChiralCauchyCarrier) =
      inner ℂ (x : CanonicalCompletedNativeChiralCauchyCarrier) (physicalRadialAdvance y)
    exact physicalRadialAdvance_isPositive.isSymmetric x y
  · intro x
    change 0 ≤ (inner ℂ (physicalRadialAdvance (x : CanonicalCompletedNativeChiralCauchyCarrier)) x).re
    exact physicalRadialAdvance_isPositive.re_inner_nonneg_left _

/-- Integer power pullback is compatible with the ORIGINAL forward advance. -/
theorem power_advance_feature (m j : ℕ) :
    powerIsometry m (nativeAdvance (physicalCauchyFeature j)) =
      (nativeAdvance^(m+1)) (powerIsometry m (physicalCauchyFeature j)) := by
  rw [native_advance_feature,power_isometry_feature,power_isometry_feature,powerColumn,powerColumn,
    map_smul,native_advance_pow_feature]
  congr 2
  unfold refinedAddress
  ring

theorem power_advance (m : ℕ) (x : PhysicalCauchySpace) :
    powerIsometry m (nativeAdvance x) = (nativeAdvance^(m+1)) (powerIsometry m x) := by
  refine physicalCauchyEmbedding_dense.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro c
  rw [embedding_sum]
  simp only [Finsupp.sum,map_sum,map_smul,power_advance_feature]

end
end CarryRadialGreen
