import QuarticError

/-! Exact rational SUFFICIENCY certificate. These four references were obtained
by evaluation of the original C3 value, not from moments or a factorization.
The theorem does NOT assert that the true source is inside these boxes. -/
namespace CarryTwoEvenJets
open CarrySelfAdjointOperator PhysicalSewing CPFormal.Analytic.Cp
open Filter Topology
open scoped BigOperators ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

/-- Rational test centers for F(0), F''(0)/2!, F(0)/4!, F''(0)/6!.
They are witness data; they do not define or replace any source coefficient. -/
def reference (j : Fin 4) : ℂ :=
  if j.val=0 then 497120778188314/1000000000000000 else
  if j.val=1 then -11485972157573/1000000000000000 else
  if j.val=2 then 123452018070/1000000000000000 else
    -832355481/1000000000000000

def fourJetTolerance : ℝ := 1/1000000000000

theorem reference_norm (j : Fin 4) : ‖reference j‖ ≤ 1/2 := by
  fin_cases j <;> norm_num [reference,Complex.norm_def]

theorem reference_quartic_lower : 1/10000000000 < (quartic reference).re := by
  norm_num [quartic,polarizedQuartic,reference,Complex.mul_re,Complex.mul_im,pow_succ]

/-- Interval sufficiency at ABSOLUTE error 10^-12 in four full Taylor jets. -/
theorem four_jet_error_suffices (v : Fin 4 → ℂ)
    (herr : ∀ j, ‖v j-reference j‖ ≤ fourJetTolerance) :
    1/20000000000 < (quartic v).re := by
  have hv : ∀ j, ‖v j‖ ≤ 1 := by
    intro j
    calc
      ‖v j‖ = ‖(v j-reference j)+reference j‖ := by ring_nf
      _ ≤ ‖v j-reference j‖+‖reference j‖ := norm_add_le _ _
      _ ≤ fourJetTolerance+1/2 := add_le_add (herr j) (reference_norm j)
      _ ≤ 1 := by norm_num [fourJetTolerance]
  have hr : ∀ j, ‖reference j‖ ≤ 1 := fun j => (reference_norm j).trans (by norm_num)
  have he := quartic_unit_error v reference fourJetTolerance (by norm_num [fourJetTolerance]) hv hr herr
  have hre := (Complex.abs_re_le_norm (quartic v-quartic reference)).trans he
  simp only [Complex.sub_re] at hre
  have hl := (abs_le.mp hre).1
  have hp := reference_quartic_lower
  norm_num [fourJetTolerance] at hl
  linarith

/-- Conditional application to the literal original source. The missing input
is four independent interval proofs; no sign or Gram hypothesis is received. -/
theorem canonical_two_even_det_pos_of_four_jet_boxes
    (herr : ∀ j, ‖nativeEvenJets j-reference j‖ ≤ fourJetTolerance) :
    0 < canonicalCompletedNativeLogDerivativeMoment 0*canonicalCompletedNativeLogDerivativeMoment 2-
      (canonicalCompletedNativeLogDerivativeMoment 1)^2 := by
  have hq : 0 < (quartic nativeEvenJets).re :=
    lt_trans (by norm_num) (four_jet_error_suffices nativeEvenJets herr)
  rw [← native_real_determinant] at hq
  exact (mul_pos_iff_of_pos_left native_center_fourth_pos).mp hq

end
end CarryTwoEvenJets
