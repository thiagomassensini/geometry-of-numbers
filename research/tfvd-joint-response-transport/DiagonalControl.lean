import JointExtraction

/-! An AUXILIARY control, not a substitution for the native source.
It refutes only the inference: exact composition + a positive radial diagonal
+ central oddness implies positivity of the full polarized form.
The test uses the unchanged physical Cauchy metric and two-port synthesis. -/
namespace CarryTfvdJoint.Control
open CarrySelfAdjointOperator PhysicalSewing NativeLaguerre ChiralReturn
open CarryTfvdCritical
open scoped BigOperators ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000

/-- A deliberately non-native analytic test response. -/
def response (z : ℂ) : ℂ := 2*z + 2*z^3 + z^5

def characteristic (z : ℂ) : ℂ := Complex.exp (-z^2-z^4/2-z^6/6)

theorem characteristic_ne_zero (z : ℂ) : characteristic z ≠ 0 :=
  Complex.exp_ne_zero _

theorem characteristic_even (z : ℂ) : characteristic (-z) = characteristic z := by
  unfold characteristic
  congr 1
  ring

/-- The test also is an actual negative logarithmic derivative of an even,
zero-free entire characteristic; it is not a list of independently assigned moments. -/
theorem response_eq_logDerivative (z : ℂ) :
    -deriv characteristic z / characteristic z = response z := by
  have hp : HasDerivAt (fun w : ℂ => -w^2-w^4/2-w^6/6)
      (-2*z-2*z^3-z^5) z := by
    apply ((((hasDerivAt_id z).pow 2).neg.sub
      (((hasDerivAt_id z).pow 4).div_const 2)).sub
      (((hasDerivAt_id z).pow 6).div_const 6)).congr_deriv
    simp only [id_eq]
    ring
  have he := hp.cexp
  have hderiv : deriv characteristic z = Complex.exp (-z^2-z^4/2-z^6/6) *
      (-2*z-2*z^3-z^5) := he.deriv
  unfold response
  rw [hderiv]
  unfold characteristic
  field_simp
  ring

theorem response_odd (z : ℂ) : response (-z) = -response z := by
  unfold response
  ring

theorem response_radial (y : ℝ) :
    response (Complex.I*(y : ℂ)) =
      Complex.I * ((2*y-2*y^3+y^5 : ℝ) : ℂ) := by
  unfold response
  push_cast
  apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im,pow_succ]
  ring

/-- EVERY positive radial point has a strictly positive diagonal.
The cross terms below nevertheless give a negative direction. -/
theorem radial_diagonal_pos (y : ℝ) (hy : 0 < y) :
    0 < (response (Complex.I*(y : ℂ))).im / (2*y) := by
  rw [response_radial]
  simp only [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, one_mul, zero_add]
  have he : 2*y-2*y^3+y^5 = y*((y^2-1)^2+1) := by ring
  rw [he]
  exact div_pos (mul_pos hy (by positivity)) (by positivity)

/-- Exact normalized response, so the control coefficients are read from
its characteristic rather than fitted to a desired matrix. -/
theorem normalized_response (z : ℂ) : response z / 2 = z + z^3 + z^5/2 := by
  unfold response
  ring

/-- First three log-derivative moments: 1, 1, 1/2.
Their entries are positive, but the second Schur residual is negative. -/
theorem second_residual_negative : (1/2 : ℝ)-1^2/1 = -1/2 := by norm_num

/-- The same fixed endpoint profile as the second even direction, with a=-1, K=10. -/
def material : Fin 4 → ℂ := ![-51,100,-50,0]

/-- A fixed endpoint input, not a changing radial test direction. -/
theorem material_endpoint :
    physicalEndpointJetInput 4 9 material = (![-1,0,-1,0] : Fin 4 → ℂ) := by
  ext a
  fin_cases a <;> norm_num [material,physicalEndpointJetInput_finite,
    Fin.sum_univ_succ,endpointGauge,nativeSourceJetOrderPhase,
    canonicalCompletedC3RadialSecondStep,canonicalGreenJetStep,pow_succ]
  apply Complex.ext <;> norm_num [Complex.mul_re,Complex.mul_im]

theorem sampled_response :
    (fun j : Fin 4 => response (canonicalCompletedC3RadialTiltPoint 9 j)) =
      ![Complex.I*(19801/100000),Complex.I*(1201/3125),
        Complex.I*(54843/100000),Complex.I*(2132/3125)] := by
  ext j
  fin_cases j <;>
    norm_num [response,canonicalCompletedC3RadialTiltPoint,canonicalCompletedC3RadialTiltStep,
      canonicalGreenJetStep,pow_succ] <;>
      apply Complex.ext <;> norm_num [Complex.mul_re,Complex.mul_im]

/-- Exact negative finite test in the ORIGINAL physical metric, retaining both legs.
No assertion is made that this auxiliary response is the Carry characteristic. -/
theorem full_original_form_negative :
    (canonicalCompletedNativeProjectiveChiralForm
      (twoPortSynthesis 4 9 material
        (fun j => response (canonicalCompletedC3RadialTiltPoint 9 j)*material j))
      (twoPortSynthesis 4 9 material
        (fun j => response (canonicalCompletedC3RadialTiltPoint 9 j)*material j))).re =
      -6199/20000 := by
  rw [twoPort_real_self]
  change portFlux 4 9 material ((fun j : Fin 4 =>
    response (canonicalCompletedC3RadialTiltPoint 9 j))*material) = _
  rw [sampled_response]
  norm_num [portFlux,matrixPairing,material,Matrix.mulVec,dotProduct,
    Fin.sum_univ_succ,cauchyMatrix,cauchyEntry]

/-- The exact same polynomial composition law holds for this control.
It therefore cannot select the sign without more information from the NATIVE source. -/
theorem composition_still_holds (a b c : ℂ) :
    jointNumerator (fun _ => 1) (fun z => -Complex.I*response z) (fun _ => 0) a c =
      jointNumerator (fun _ => 1) (fun z => -Complex.I*response z) (fun _ => 0) a b +
      jointNumerator (fun _ => 1) (fun z => -Complex.I*response z) (fun _ => 0) b c := by
  simpa only [one_mul] using jointNumerator_cocycle
    (fun _ => (1 : ℂ)) (fun z => -Complex.I*response z) (fun _ => 0) a b c

end
end CarryTfvdJoint.Control
