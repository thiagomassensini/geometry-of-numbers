import GeometryOfNumbers.Analysis.C2GlobalGreenBridge
import Lean

open Lean Elab Command
elab "#assert_c2_bridge_axioms " id:ident : command => do
  let decl ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let deps ← collectAxioms decl
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for name in deps do
    unless allowed.contains name do
      throwError "Unexpected foundational dependency: {decl} depends on {name}"

namespace GeometryOfNumbers.Analysis.C2GlobalGreenBridge
open GeometryOfNumbers.Analysis GreenFrame.Concrete
open scoped lp ENNReal InnerProductSpace

#assert_c2_bridge_axioms realPlaneToComplexIsometry
#print axioms realPlaneToComplexIsometry
#assert_c2_bridge_axioms realPlaneToComplexIsometry_re
#print axioms realPlaneToComplexIsometry_re
#assert_c2_bridge_axioms realPlaneToComplexIsometry_im
#print axioms realPlaneToComplexIsometry_im
#assert_c2_bridge_axioms realPlaneToComplexIsometry_normSq
#print axioms realPlaneToComplexIsometry_normSq
#assert_c2_bridge_axioms oddMaterialGreenCoordinates
#print axioms oddMaterialGreenCoordinates
#assert_c2_bridge_axioms oddMaterialToGreenState
#print axioms oddMaterialToGreenState
#assert_c2_bridge_axioms oddMaterialToGreenState_apply
#print axioms oddMaterialToGreenState_apply
#assert_c2_bridge_axioms oddMaterialToGreenState_apply_off_sector
#print axioms oddMaterialToGreenState_apply_off_sector
#assert_c2_bridge_axioms oddMaterialToGreenState_one
#print axioms oddMaterialToGreenState_one
#assert_c2_bridge_axioms oddMaterialToGreenState_even
#print axioms oddMaterialToGreenState_even
#assert_c2_bridge_axioms oddMaterialToGreenState_norm
#print axioms oddMaterialToGreenState_norm
#assert_c2_bridge_axioms c2GlobalGreenInputIsometry
#print axioms c2GlobalGreenInputIsometry
#assert_c2_bridge_axioms c2GlobalGreenInput_norm
#print axioms c2GlobalGreenInput_norm
#assert_c2_bridge_axioms c2GlobalGreenInput_apply
#print axioms c2GlobalGreenInput_apply
#assert_c2_bridge_axioms c2GlobalGreenInput_one
#print axioms c2GlobalGreenInput_one
#assert_c2_bridge_axioms c2GlobalGreenInput_even
#print axioms c2GlobalGreenInput_even
#assert_c2_bridge_axioms c2GlobalGreenInput_provenance
#print axioms c2GlobalGreenInput_provenance
#assert_c2_bridge_axioms c2GlobalGreenAnalysis
#print axioms c2GlobalGreenAnalysis
#assert_c2_bridge_axioms c2GlobalGreenAnalysis_apply
#print axioms c2GlobalGreenAnalysis_apply
#assert_c2_bridge_axioms c2GlobalGreenAnalysis_norm_sq_bounds
#print axioms c2GlobalGreenAnalysis_norm_sq_bounds
#assert_c2_bridge_axioms c2GlobalGreenAnalysis_split_seedResidual_green
#print axioms c2GlobalGreenAnalysis_split_seedResidual_green
#assert_c2_bridge_axioms c2GlobalGreenAnalysis_split_external_bulk
#print axioms c2GlobalGreenAnalysis_split_external_bulk
#assert_c2_bridge_axioms c2GlobalGreenAnalysis_split_three
#print axioms c2GlobalGreenAnalysis_split_three
#assert_c2_bridge_axioms c2GlobalRawGreenDefect
#print axioms c2GlobalRawGreenDefect
#assert_c2_bridge_axioms realPlaneToComplexIsometry_scale_rotate
#print axioms realPlaneToComplexIsometry_scale_rotate
#assert_c2_bridge_axioms realPlaneToComplexIsometry_coordinate_roundtrip
#print axioms realPlaneToComplexIsometry_coordinate_roundtrip
#assert_c2_bridge_axioms c2GlobalGreenInput_closed_form
#print axioms c2GlobalGreenInput_closed_form
#assert_c2_bridge_axioms c2GlobalRawGreenDefect_split
#print axioms c2GlobalRawGreenDefect_split
#assert_c2_bridge_axioms c2GlobalRawGreenDefect_bounds
#print axioms c2GlobalRawGreenDefect_bounds
#assert_c2_bridge_axioms c2GlobalRestrictedGreenGram
#print axioms c2GlobalRestrictedGreenGram
#assert_c2_bridge_axioms c2GlobalRestrictedGreenGram_inner
#print axioms c2GlobalRestrictedGreenGram_inner
#assert_c2_bridge_axioms c2GlobalRestrictedGreenGram_positive
#print axioms c2GlobalRestrictedGreenGram_positive
#assert_c2_bridge_axioms c2GlobalRestrictedGreenGram_bounds
#print axioms c2GlobalRestrictedGreenGram_bounds
#assert_c2_bridge_axioms c2GlobalRestrictedGreenGram_isUnit
#print axioms c2GlobalRestrictedGreenGram_isUnit
#assert_c2_bridge_axioms c2GlobalRestrictedGreenGram_bijective
#print axioms c2GlobalRestrictedGreenGram_bijective
#assert_c2_bridge_axioms c2GlobalRestrictedGreenGram_strictlyPositive
#print axioms c2GlobalRestrictedGreenGram_strictlyPositive
#assert_c2_bridge_axioms c2GlobalRestrictedGreenGram_compression
#print axioms c2GlobalRestrictedGreenGram_compression
#assert_c2_bridge_axioms c2GlobalRestrictedGreenGram_source_factors
#print axioms c2GlobalRestrictedGreenGram_source_factors
#assert_c2_bridge_axioms c2GlobalGreenInput_adjoint_comp_self
#print axioms c2GlobalGreenInput_adjoint_comp_self
#assert_c2_bridge_axioms c2GlobalSource_adjoint_comp_self
#print axioms c2GlobalSource_adjoint_comp_self
#assert_c2_bridge_axioms oddMaterialToGreenState_adjoint_comp_self
#print axioms oddMaterialToGreenState_adjoint_comp_self
#assert_c2_bridge_axioms c2GlobalRawGreenDefect_eq_gram_defect
#print axioms c2GlobalRawGreenDefect_eq_gram_defect
#assert_c2_bridge_axioms c2GlobalRestrictedGreenGram_eq_one_iff_norm
#print axioms c2GlobalRestrictedGreenGram_eq_one_iff_norm
#assert_c2_bridge_axioms c2GlobalRestrictedGreenGram_eq_one_iff_defect_zero
#print axioms c2GlobalRestrictedGreenGram_eq_one_iff_defect_zero
#assert_c2_bridge_axioms c2GlobalGreenInput_quadrature_roundtrip
#print axioms c2GlobalGreenInput_quadrature_roundtrip
#assert_c2_bridge_axioms c2GlobalGreenInput_seedResidual_eq_residual
#print axioms c2GlobalGreenInput_seedResidual_eq_residual
#assert_c2_bridge_axioms c2GlobalGreenAnalysis_split_residual_depthOne_bulk
#print axioms c2GlobalGreenAnalysis_split_residual_depthOne_bulk
#assert_c2_bridge_axioms c2GlobalRawGreenDefect_zero
#print axioms c2GlobalRawGreenDefect_zero

-- Formal composition checks, rather than a numerical metric test.
example (v : RealPlaneHilbert) :
    Complex.normSq (realPlaneToComplexIsometry v) =
      realPlaneEnergy (realPlaneHilbertEquiv.symm v) := realPlaneToComplexIsometry_normSq v
example (x : OddMaterialState) : ‖oddMaterialToGreenState x‖ = ‖x‖ := oddMaterialToGreenState_norm x
example (x : OddMaterialState) : oddMaterialToGreenState x 1 = 0 := oddMaterialToGreenState_one x
example (x : OddMaterialState) : oddMaterialToGreenState x (2 : PNat) = 0 :=
  oddMaterialToGreenState_even x 2 (by norm_num)
example (t : ℝ) (v : CoreState) : ‖c2GlobalGreenInputIsometry t v‖ = ‖v‖ :=
  c2GlobalGreenInput_norm t v
example (t : ℝ) (v : CoreState) :
    (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ ‖c2GlobalGreenAnalysis t v‖ ^ 2 :=
  (c2GlobalGreenAnalysis_norm_sq_bounds t v).1
example (t : ℝ) : (c2GlobalRestrictedGreenGram t).IsPositive :=
  c2GlobalRestrictedGreenGram_positive t
example (t : ℝ) : IsUnit (c2GlobalRestrictedGreenGram t) := c2GlobalRestrictedGreenGram_isUnit t
example (t : ℝ) : c2GlobalRawGreenDefect t 0 = 0 := c2GlobalRawGreenDefect_zero t

end GeometryOfNumbers.Analysis.C2GlobalGreenBridge
