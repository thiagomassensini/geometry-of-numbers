import GeometryOfNumbers.Analysis.CarryMaterialSourceRealization
import GeometryOfNumbers.Analysis.QuadraticCenteredBracket

/-! Dilation of the ORIGINAL material samples and both positional legs.
Address dilation is a phase translation of the material clock, not a
rescaling of its frequencies or an asserted scaling of canonical moments. -/
namespace GeometryOfNumbers.Analysis.CarryScale
open BaseTwoCompletion
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

theorem inverse_sqrt_mul (q x : ℝ) (hq : 0 ≤ q) :
    (Real.sqrt (q*x))⁻¹ = (Real.sqrt q)⁻¹ * (Real.sqrt x)⁻¹ := by
  rw [Real.sqrt_mul hq, mul_inv]

theorem centered_inverse_sqrt_dilate (q C a : ℝ) (hq : 0 < q) :
    realCenteredReadout (Real.sqrt (q*C-q*a))⁻¹ (Real.sqrt (q*C))⁻¹
        (Real.sqrt (q*C+q*a))⁻¹ =
      (Real.sqrt q)⁻¹ * realCenteredReadout (Real.sqrt (C-a))⁻¹
        (Real.sqrt C)⁻¹ (Real.sqrt (C+a))⁻¹ := by
  rw [show q*C-q*a=q*(C-a) by ring, show q*C+q*a=q*(C+a) by ring]
  simp only [inverse_sqrt_mul q _ hq.le, realCenteredReadout]
  ring

theorem centered_relative_defect_dilate (q C a : ℝ) (hq : 0 < q) :
    realCenteredReadout (Real.sqrt (q*C-q*a))⁻¹ (Real.sqrt (q*C))⁻¹
        (Real.sqrt (q*C+q*a))⁻¹ / (Real.sqrt (q*C))⁻¹ =
      realCenteredReadout (Real.sqrt (C-a))⁻¹ (Real.sqrt C)⁻¹
        (Real.sqrt (C+a))⁻¹ / (Real.sqrt C)⁻¹ := by
  rw [centered_inverse_sqrt_dilate q C a hq, inverse_sqrt_mul q C hq.le]
  exact mul_div_mul_left _ _ (inv_ne_zero (Real.sqrt_pos.mpr hq).ne')

/-- The relative defect depends only on the positional ratio a/C. -/
theorem centered_relative_defect_shape (C a : ℝ) (hC : 0 < C) :
    realCenteredReadout (Real.sqrt (C-a))⁻¹ (Real.sqrt C)⁻¹ (Real.sqrt (C+a))⁻¹ /
        (Real.sqrt C)⁻¹ =
      realCenteredReadout (Real.sqrt (1-a/C))⁻¹ 1 (Real.sqrt (1+a/C))⁻¹ := by
  have h := centered_relative_defect_dilate C⁻¹ C a (inv_pos.mpr hC)
  simpa [hC.ne', div_eq_mul_inv, mul_comm] using h.symm

theorem amplitude_eq_inverse_sqrt_depth (b k : ℕ) (hb : 0 < b) :
    realCriticalAmplitude b k hb = (Real.sqrt ((b:ℝ)^k))⁻¹ := by
  have ha : 0 < realCriticalAmplitude b k hb := by
    rw [realCriticalAmplitude_eq_rpow]; exact Real.rpow_pos_of_pos (Nat.cast_pos.mpr hb) _
  have hs := realCriticalAmplitude_sq_eq_realDepthMass b k hb
  rw [realDepthMass_eq_inv_pow] at hs
  have hp : 0 ≤ (Real.sqrt ((b:ℝ)^k))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hsq : ((Real.sqrt ((b:ℝ)^k))⁻¹)^2 = ((b:ℝ)^k)⁻¹ := by
    have ht := congrArg (fun x : ℝ => x⁻¹)
      (Real.sq_sqrt (pow_nonneg (Nat.cast_nonneg b) k))
    simpa only [inv_pow] using ht
  nlinarith

/-- Exact amplitude AND phase of address dilation, before any scalar readout. -/
theorem material_sample_dilate (q n : ℕ) (hq : 0 < q) (hn : 0 < n) (t : ℝ) :
    criticalMaterialSample t (q*n) =
      ((Real.sqrt (q:ℝ))⁻¹ : ℂ) *
        Complex.exp (-(((t*Real.log (q:ℝ) : ℝ):ℂ)*Complex.I)) *
          criticalMaterialSample t n := by
  have hqr : (q:ℝ) ≠ 0 := (Nat.cast_pos.mpr hq).ne'
  have hnr : (n:ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
  simp only [criticalMaterialSample, Nat.cast_mul,
    inverse_sqrt_mul (q:ℝ) (n:ℝ) (Nat.cast_nonneg q), Real.log_mul hqr hnr]
  rw [show -(((t*(Real.log (q:ℝ)+Real.log (n:ℝ)) : ℝ):ℂ)*Complex.I) =
      -(((t*Real.log (q:ℝ):ℝ):ℂ)*Complex.I) +
        -(((t*Real.log (n:ℝ):ℝ):ℂ)*Complex.I) by push_cast; ring]
  rw [Complex.exp_add]
  push_cast
  ring

/-- The three ordered addresses remain present; neither leg is collapsed. -/
theorem material_three_addresses_dilate (q l c r : ℕ) (hq : 0 < q)
    (hl : 0 < l) (hc : 0 < c) (hr : 0 < r) (t : ℝ) :
    criticalMaterialSample t (q*l)-2*criticalMaterialSample t (q*c)+
        criticalMaterialSample t (q*r) =
      (((Real.sqrt (q:ℝ))⁻¹ : ℂ)*Complex.exp (-(((t*Real.log (q:ℝ):ℝ):ℂ)*Complex.I))) *
        (criticalMaterialSample t l-2*criticalMaterialSample t c+criticalMaterialSample t r) := by
  rw [material_sample_dilate q l hq hl, material_sample_dilate q c hq hc,
    material_sample_dilate q r hq hr]
  ring

end
end GeometryOfNumbers.Analysis.CarryScale
