import NativeCoefficient

namespace CarryCurvatureGreen
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd NativeLaguerre
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

/-- Literal factorial-normalized shape of the OLD fourth forward difference. -/
def fourthShape : ℕ →₀ ℂ := ∑ j ∈ Finset.range 5,
  (completedGreenForwardWeight 4 j/(Nat.factorial 4 : ℂ)) • Finsupp.single j 1

/-- The direct repeated-complement lift is a candidate, not a new source. -/
def liftedFourthSeed : PhysicalSpace := (-(1/12) : ℂ) •
  physicalComplement (physicalComplement (completedNativeChiralCauchyFeature 0))

theorem fourth_shape_explicit : fourthShape=
    Finsupp.single 0 (1/24) + Finsupp.single 1 (-(1/6)) + Finsupp.single 2 (1/4) +
      Finsupp.single 3 (-(1/6)) + Finsupp.single 4 (1/24) := by
  have hc : Nat.choose 4 2=6 := by decide
  norm_num [fourthShape,Finset.sum_range_succ,completedGreenForwardWeight,hc]

theorem fourth_shape_synthesis : physicalCauchySynthesis fourthShape=
    (1/24 : ℂ) • completedNativeChiralCauchyFeature 0 - (1/6 : ℂ) • completedNativeChiralCauchyFeature 1 +
      (1/4 : ℂ) • completedNativeChiralCauchyFeature 2 - (1/6 : ℂ) • completedNativeChiralCauchyFeature 3 +
      (1/24 : ℂ) • completedNativeChiralCauchyFeature 4 := by
  simp only [fourth_shape_explicit,physicalCauchySynthesis,map_add,Finsupp.linearCombination_single]
  module

theorem fourth_native_curvature : physicalCurvature liftedFourthSeed=physicalCauchySynthesis fourthShape := by
  rw [fourth_shape_synthesis]
  simp only [physicalCurvature,liftedFourthSeed,physicalComplement,sub_apply,one_apply_eq_self,
    map_sub,map_smul,physicalRadialAdvance_feature]
  module

theorem fourth_commutator (eta : ℝ) : completionCommutator eta (monomialWeight 1) fourthShape=
    Finsupp.single 1 ((eta : ℂ)⁻¹/4-(eta : ℂ)/24) +
    Finsupp.single 2 (-(eta : ℂ)⁻¹/6+(eta : ℂ)/6) +
    Finsupp.single 3 ((eta : ℂ)⁻¹/24-(eta : ℂ)/4) +
    Finsupp.single 4 ((eta : ℂ)/6) + Finsupp.single 5 (-(eta : ℂ)/24) := by
  ext j
  rcases j with _ | _ | _ | _ | _ | _ | j
  all_goals simp [completion_commutator_zero,completion_commutator_succ,fourth_shape_explicit,monomialWeight] <;> ring

/-- The curvature lift alone misses this EXACT native commutator boundary.
No term is discarded or absorbed into a modified metric. -/
theorem fourth_tangent_defect (eta : ℝ) :
    physicalCauchySynthesis (completionCommutator eta (monomialWeight 1) fourthShape)=
      physicalTangent eta liftedFourthSeed + (eta : ℂ)⁻¹ •
        ((5/24 : ℂ) • completedNativeChiralCauchyFeature 1-
          (1/12 : ℂ) • completedNativeChiralCauchyFeature 2) := by
  rw [fourth_commutator]
  simp only [physicalCauchySynthesis,map_add,Finsupp.linearCombination_single]
  unfold physicalTangent
  rw [fourth_native_curvature,fourth_shape_synthesis]
  simp only [liftedFourthSeed,physicalComplement,sub_apply,one_apply_eq_self,map_sub,map_smul,
    map_add,physicalRadialAdvance_feature]
  module

theorem fourth_tangent_not_direct_lift (eta : ℝ) (h0 : 0 < eta) :
    physicalCauchySynthesis (completionCommutator eta (monomialWeight 1) fourthShape) ≠
      physicalTangent eta liftedFourthSeed := by
  have hd : (5/24 : ℂ) • completedNativeChiralCauchyFeature 1-
      (1/12 : ℂ) • completedNativeChiralCauchyFeature 2 ≠ 0 := by
    intro hz
    have hh := congrArg (fun f : PhysicalSpace => inner ℂ (completedNativeChiralCauchyFeature 1) f) hz
    simp only [inner_sub_right,inner_smul_right,inner_zero_right,
      inner_completedNativeChiralCauchyFeature] at hh
    norm_num at hh
  have he : (eta : ℂ)⁻¹ ≠ 0 := inv_ne_zero (Complex.ofReal_ne_zero.mpr h0.ne')
  have hn := smul_ne_zero he hd
  intro hwrong
  have hh := fourth_tangent_defect eta
  rw [hwrong] at hh
  apply hn
  apply add_left_cancel (a := physicalTangent eta liftedFourthSeed)
  simpa only [add_zero] using hh.symm

end
end CarryCurvatureGreen
