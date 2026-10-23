import ReadoutResidual

/-! The actual radial phase is already inside nativeHeatGreenPort. The only
inverse used here removes the nonzero Gamma factor proved by the Mellin
identity. No scalar Wronskian or desired moment defines this port. -/
namespace CarryGreenProvenance
open CarryFourLeg CarryCameraTail CarryMaterialTheta CarrySelfAdjointOperator
open CPFormal.Analytic.Cp NativeCarryC3Crosswalk NativeCarrySpectralWeyl.Boundary
noncomputable section
set_option autoImplicit false

def materialGreenPort (N : ℕ) (s : ℂ) : FiniteC3GreenPortCarrier N :=
  (Complex.Gammaℝ s)⁻¹ • cellwiseMellinPort N (nativeHeatGreenPort N s) s

theorem material_green_port_eq (N : ℕ) {s : ℂ} (hs : 0 < s.re) :
    materialGreenPort N s = finiteC3GenuineBracketGreenBoundaryPair N s := by
  rw [materialGreenPort, native_green_port_mellin N hs, smul_smul,
    inv_mul_cancel₀ (Complex.Gammaℝ_ne_zero_of_re_pos hs), one_smul]

theorem reflected_re_pos {z : ℂ} (hz : z.re < 1) :
    0 < (reflectedParameter z).re := by
  rw [reflectedParameter_re]
  linarith

/-- The direct port of the MIXED pair depends on its value at w, not on
its independent log-jet parameter z. -/
theorem mixed_direct_green_port (M : ℕ) (z w : ℂ) :
    (finiteC3EnrichedTfvdPairTransport M tfvdHaarScale (fun _ => 1) w
      (canonicalMixedBoundaryResidualPair tfvdHaarScale (fun _ => 1) z w)).greenPort =
      finiteC3GenuineBracketGreenBoundaryPair (M*3) w := by
  exact finiteC3EnrichedTfvdValueGreenPort_canonical M tfvdHaarScale_ne_zero
    (fun _ => 1) (by simp) w

theorem reflected_green_port (M : ℕ) (z : ℂ) :
    (finiteC3EnrichedTfvdPairTransport M tfvdHaarScale (fun _ => 1)
      (reflectedParameter z)
      (canonicalBoundaryResidualPair tfvdHaarScale (fun _ => 1)
        (reflectedParameter z))).greenPort =
      finiteC3GenuineBracketGreenBoundaryPair (M*3) (reflectedParameter z) := by
  exact finiteC3EnrichedTfvdValueGreenPort_canonical M tfvdHaarScale_ne_zero
    (fun _ => 1) (by simp) (reflectedParameter z)

theorem direct_port_mellin (M : ℕ) (z : ℂ) {w : ℂ} (hw : 0 < w.re) :
    materialGreenPort (M*3) w =
      (finiteC3EnrichedTfvdPairTransport M tfvdHaarScale (fun _ => 1) w
        (canonicalMixedBoundaryResidualPair tfvdHaarScale (fun _ => 1) z w)).greenPort := by
  rw [material_green_port_eq _ hw, mixed_direct_green_port]

theorem reflected_port_mellin (M : ℕ) {z : ℂ} (hz : z.re < 1) :
    materialGreenPort (M*3) (reflectedParameter z) =
      (finiteC3EnrichedTfvdPairTransport M tfvdHaarScale (fun _ => 1)
        (reflectedParameter z)
        (canonicalBoundaryResidualPair tfvdHaarScale (fun _ => 1)
          (reflectedParameter z))).greenPort := by
  rw [material_green_port_eq _ (reflected_re_pos hz), reflected_green_port]

/-- Every residue of the Green port is kept before the pairing. -/
theorem green_edge_mellin (N : ℕ) (i : Fin N) {s t : ℂ}
    (hs : 0 < s.re) (ht : 0 < t.re) :
    finiteC3GreenPortEdge (materialGreenPort N s) (materialGreenPort N t) i =
      finiteC3GreenPortEdge (finiteC3GenuineBracketGreenBoundaryPair N s)
        (finiteC3GenuineBracketGreenBoundaryPair N t) i := by
  rw [material_green_port_eq N hs, material_green_port_eq N ht]

theorem green_form_mellin (N : ℕ) {s t : ℂ}
    (hs : 0 < s.re) (ht : 0 < t.re) :
    greenForm (𝕜 := ℂ) (materialGreenPort N s) (materialGreenPort N t) =
      greenForm (𝕜 := ℂ) (finiteC3GenuineBracketGreenBoundaryPair N s)
        (finiteC3GenuineBracketGreenBoundaryPair N t) := by
  rw [material_green_port_eq N hs, material_green_port_eq N ht]

end
end CarryGreenProvenance
