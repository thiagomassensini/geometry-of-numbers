import RadialRefinement

namespace CarryRadialRefinement
open CarryPhysicalTrace CarrySelfAdjointOperator CarrySelfAdjointOperator.NativeLaguerre
open scoped BigOperators ComplexConjugate InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

theorem power_composition_feature (m n j : ℕ) :
    powerIsometry m (powerIsometry n (physicalCauchyFeature j)) =
      powerIsometry (refinedAddress m n) (physicalCauchyFeature j) := by
  have h0 : radialVector 0 j = physicalCauchyFeature j := by
    rw [radial_vector_feature]
    norm_num
  rw [← h0,power_isometry_radial,power_isometry_radial,power_isometry_radial]
  simp only [refinedAddress,zero_add,mul_zero]
  congr 1
  ring

/-- Coherence is vectorial on the entire original physical closure, not just
an equality of readouts or norms. Surjectivity/unitarity is not presumed. -/
theorem power_composition (m n : ℕ) (x : PhysicalCauchySpace) :
    powerIsometry m (powerIsometry n x) = powerIsometry (refinedAddress m n) x := by
  refine physicalCauchyEmbedding_dense.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro c
  rw [embedding_sum]
  simp only [Finsupp.sum,map_sum,map_smul,power_composition_feature]

theorem power_identity (x : PhysicalCauchySpace) : powerIsometry 0 x = x := by
  refine physicalCauchyEmbedding_dense.induction_on x (isClosed_eq (by fun_prop) continuous_id) ?_
  intro c
  rw [embedding_sum]
  simp only [Finsupp.sum,map_sum,map_smul,power_isometry_feature,powerColumn]
  simp [refinedAddress]

/-- Distinct representations of the SAME radial spectral node have identical
transported full chiral states in their common grade. Original material/camera
states are not identified merely because one scalar readout agrees. -/
theorem equal_radial_point_common_states (k l i j : ℕ)
    (hp : canonicalCompletedC3RadialTiltPoint k i = canonicalCompletedC3RadialTiltPoint l j) :
    pairPower l (projectiveLegs k i) = pairPower k (projectiveLegs l j) := by
  have hg : refinedAddress k l = refinedAddress l k := common_grade_comm l k
  have he : canonicalCompletedC3RadialTiltPoint (refinedAddress l k) (refinedAddress l i) =
      canonicalCompletedC3RadialTiltPoint (refinedAddress l k) (refinedAddress k j) := by
    rw [refined_point,← hg,refined_point]
    exact hp
  have him := congrArg Complex.im he
  rw [canonicalCompletedC3RadialTiltPoint_im,canonicalCompletedC3RadialTiltPoint_im] at him
  have hd : ((refinedAddress l k : ℝ)+1) ≠ 0 := by positivity
  have ha : refinedAddress l i = refinedAddress k j := by
    have hh := (div_left_inj' hd).mp him
    exact_mod_cast (by linarith : (refinedAddress l i : ℝ) = (refinedAddress k j : ℝ))
  rw [pair_power_refines_projective,pair_power_refines_projective,hg,ha]

end
end CarryRadialRefinement
