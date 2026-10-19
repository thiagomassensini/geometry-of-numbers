import GeometryOfNumbers.Analysis.CarryScaleGeometry
import GeometryOfNumbers.Analysis.MomentScaleElimination
import GeometryOfNumbers.Analysis.MomentScaleHeight
import GeometryOfNumbers.Analysis.LogDerivativeScale
import Lean
open Lean Elab Command
elab "#audit_carry_scale " ids:ident+ : command => do
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let mut todo : List Name := []
  for id in ids do
    let decl ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    todo := decl :: todo
    for name in (← collectAxioms decl) do
      unless allowed.contains name do
        throwError "Unexpected foundational dependency: {decl} depends on {name}"
  let mut seen : NameSet := {}
  while !todo.isEmpty do
    let name := todo.head!
    todo := todo.tail!
    if !seen.contains name then
      seen := seen.insert name
      if let some info := env.find? name then
        match info with
        | .axiomInfo _ =>
          unless allowed.contains name do
            throwError "Unverified dependency: {name}"
        | _ => pure ()
        todo := info.type.getUsedConstants.toList ++ todo
        if let some value := info.value? then
          todo := value.getUsedConstants.toList ++ todo
  logInfo m!"Carry scale roots: {ids.size}; type/body closure: {seen.size}; foundational guard passed"

#print axioms GeometryOfNumbers.Analysis.CarryScale.massScaledMoment
#print axioms GeometryOfNumbers.Analysis.CarryScale.diagonalScale
#print axioms GeometryOfNumbers.Analysis.CarryScale.scaledInverseFactor
#print axioms GeometryOfNumbers.Analysis.CarryScale.scaledWhitening
#print axioms GeometryOfNumbers.Analysis.CarryScale.inverse_sqrt_mul
#print axioms GeometryOfNumbers.Analysis.CarryScale.centered_inverse_sqrt_dilate
#print axioms GeometryOfNumbers.Analysis.CarryScale.centered_relative_defect_dilate
#print axioms GeometryOfNumbers.Analysis.CarryScale.centered_relative_defect_shape
#print axioms GeometryOfNumbers.Analysis.CarryScale.amplitude_eq_inverse_sqrt_depth
#print axioms GeometryOfNumbers.Analysis.CarryScale.material_sample_dilate
#print axioms GeometryOfNumbers.Analysis.CarryScale.material_three_addresses_dilate
#print axioms GeometryOfNumbers.Analysis.CarryScale.scaled_hankel
#print axioms GeometryOfNumbers.Analysis.CarryScale.scaled_shifted
#print axioms GeometryOfNumbers.Analysis.CarryScale.elimination_scale
#print axioms GeometryOfNumbers.Analysis.CarryScale.pivot_scale
#print axioms GeometryOfNumbers.Analysis.CarryScale.column_scale
#print axioms GeometryOfNumbers.Analysis.CarryScale.cholesky_scale
#print axioms GeometryOfNumbers.Analysis.CarryScale.hankel_pivot_scale
#print axioms GeometryOfNumbers.Analysis.CarryScale.hankel_cholesky_scale
#print axioms GeometryOfNumbers.Analysis.CarryScale.pivot_ratio_invariant
#print axioms GeometryOfNumbers.Analysis.CarryScale.sector_pivot_scale
#print axioms GeometryOfNumbers.Analysis.CarryScale.hankel_pivot_sign
#print axioms GeometryOfNumbers.Analysis.CarryScale.fixed_moment_scale_rigid
#print axioms GeometryOfNumbers.Analysis.CarryScale.scaled_whitening
#print axioms GeometryOfNumbers.Analysis.CarryScale.jacobi_scale
#print axioms GeometryOfNumbers.Analysis.CarryScale.jacobi_section_scale
#print axioms GeometryOfNumbers.Analysis.CarryScale.jacobi_mass_blind
#print axioms GeometryOfNumbers.Analysis.CarryScale.cholesky_inverse_scale
#print axioms GeometryOfNumbers.Analysis.CarryScale.cholesky_jacobi_scale
#print axioms GeometryOfNumbers.Analysis.CarryScale.finite_height_scale
#print axioms GeometryOfNumbers.Analysis.CarryScale.finite_height_depth_scale
#print axioms GeometryOfNumbers.Analysis.CarryScale.log_sequence_dilate
#print axioms GeometryOfNumbers.Analysis.CarryScale.log_moments_dilate
#print axioms GeometryOfNumbers.Analysis.CarryScale.log_moments_constant_amplitude
#print axioms GeometryOfNumbers.Analysis.CarryScale.response_dilation_mass
#print axioms GeometryOfNumbers.Analysis.CarryScale.geometric_mass_not_response_dilation
#print axioms GeometryOfNumbers.Analysis.CarryScale.log_response_phase

#audit_carry_scale
  GeometryOfNumbers.Analysis.CarryScale.massScaledMoment
  GeometryOfNumbers.Analysis.CarryScale.diagonalScale
  GeometryOfNumbers.Analysis.CarryScale.scaledInverseFactor
  GeometryOfNumbers.Analysis.CarryScale.scaledWhitening
  GeometryOfNumbers.Analysis.CarryScale.inverse_sqrt_mul
  GeometryOfNumbers.Analysis.CarryScale.centered_inverse_sqrt_dilate
  GeometryOfNumbers.Analysis.CarryScale.centered_relative_defect_dilate
  GeometryOfNumbers.Analysis.CarryScale.centered_relative_defect_shape
  GeometryOfNumbers.Analysis.CarryScale.amplitude_eq_inverse_sqrt_depth
  GeometryOfNumbers.Analysis.CarryScale.material_sample_dilate
  GeometryOfNumbers.Analysis.CarryScale.material_three_addresses_dilate
  GeometryOfNumbers.Analysis.CarryScale.scaled_hankel
  GeometryOfNumbers.Analysis.CarryScale.scaled_shifted
  GeometryOfNumbers.Analysis.CarryScale.elimination_scale
  GeometryOfNumbers.Analysis.CarryScale.pivot_scale
  GeometryOfNumbers.Analysis.CarryScale.column_scale
  GeometryOfNumbers.Analysis.CarryScale.cholesky_scale
  GeometryOfNumbers.Analysis.CarryScale.hankel_pivot_scale
  GeometryOfNumbers.Analysis.CarryScale.hankel_cholesky_scale
  GeometryOfNumbers.Analysis.CarryScale.pivot_ratio_invariant
  GeometryOfNumbers.Analysis.CarryScale.sector_pivot_scale
  GeometryOfNumbers.Analysis.CarryScale.hankel_pivot_sign
  GeometryOfNumbers.Analysis.CarryScale.fixed_moment_scale_rigid
  GeometryOfNumbers.Analysis.CarryScale.scaled_whitening
  GeometryOfNumbers.Analysis.CarryScale.jacobi_scale
  GeometryOfNumbers.Analysis.CarryScale.jacobi_section_scale
  GeometryOfNumbers.Analysis.CarryScale.jacobi_mass_blind
  GeometryOfNumbers.Analysis.CarryScale.cholesky_inverse_scale
  GeometryOfNumbers.Analysis.CarryScale.cholesky_jacobi_scale
  GeometryOfNumbers.Analysis.CarryScale.finite_height_scale
  GeometryOfNumbers.Analysis.CarryScale.finite_height_depth_scale
  GeometryOfNumbers.Analysis.CarryScale.log_sequence_dilate
  GeometryOfNumbers.Analysis.CarryScale.log_moments_dilate
  GeometryOfNumbers.Analysis.CarryScale.log_moments_constant_amplitude
  GeometryOfNumbers.Analysis.CarryScale.response_dilation_mass
  GeometryOfNumbers.Analysis.CarryScale.geometric_mass_not_response_dilation
  GeometryOfNumbers.Analysis.CarryScale.log_response_phase
