import FourthDifference

namespace CarryFourthTail
open GeometryOfNumbers.Analysis GeometryOfNumbers.Analysis.BaseTwoCompletion
open CarryCellTail CarryMaterialParts Filter Topology
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

theorem complex_first_bound (a : ℕ) (ha : 0 < a) (w : ℂ) (hw : ‖w‖ ≤ (1/2:ℝ)) :
    ‖complexSample (a+1) w-complexSample a w‖ ≤ 1/(a:ℝ) := by
  let z := baseTwoComplexMaterialExponent w
  have ha0 : (0:ℝ) < a := by exact_mod_cast ha
  have ha1 : (1:ℝ) ≤ a := by exact_mod_cast ha
  obtain ⟨hre,hz⟩ := exponent_closed_half w hw
  have hb (x : ℝ) (hx : x ∈ Set.Icc (a:ℝ) (a+1)) :
      ‖z*(x:ℂ)^(z-1)‖ ≤ 1/(a:ℝ) := by
    have hx0 := ha0.trans_le hx.1
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    have he : (z-1).re ≤ (-1:ℝ) := by simp only [Complex.sub_re, Complex.one_re]; linarith
    have hp := (Real.rpow_le_rpow_of_exponent_le (ha1.trans hx.1) he).trans
      (Real.rpow_le_rpow_of_nonpos ha0 hx.1 (by norm_num))
    have h := mul_le_mul hz hp (Real.rpow_nonneg hx0.le _) (by norm_num : (0:ℝ) ≤ 1)
    simpa only [Real.rpow_neg_one, one_mul, one_div] using h
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x hx => (cpow_spatial_derivative z x (ha0.trans_le hx.1)).hasDerivWithinAt)
    hb (convex_Icc (a:ℝ) (a+1))
    (by constructor <;> linarith : (a:ℝ) ∈ Set.Icc (a:ℝ) (a+1))
    (by constructor <;> linarith : (a:ℝ)+1 ∈ Set.Icc (a:ℝ) (a+1))
  simpa only [show (a:ℝ)+1-a=1 by ring, norm_one, mul_one, complexSample,
    Nat.cast_add, Nat.cast_one, Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one] using h

theorem complex_boundary_entire (a : ℕ) (ha : 0 < a) : Differentiable ℂ (complexBoundary a) := by
  unfold complexBoundary tailBoundary
  exact ((((complex_sample_entire _ (by omega)).const_mul 3).sub
    ((complex_sample_entire _ (by omega)).const_mul 8)).add
    ((complex_sample_entire _ ha).const_mul 5)).div_const 8

theorem complex_remainder_entire (a : ℕ) (ha : 0 < a) : Differentiable ℂ (complexRemainder a) := by
  unfold complexRemainder tailRemainder
  exact (((complex_fourth_entire a ha).const_mul (3/8:ℂ)).add
    ((complex_fourth_entire _ (by omega)).const_mul (1/2:ℂ))).add
    ((complex_fourth_entire _ (by omega)).const_mul (3/8:ℂ))

theorem complex_boundary_bound (a : ℕ) (ha : 0 < a) (w : ℂ) (hw : ‖w‖ ≤ (1/2:ℝ)) :
    ‖complexBoundary a w‖ ≤ 1/(a:ℝ) := by
  have he : complexBoundary a w =
      (3/8:ℂ)*(complexSample (a+2) w-complexSample (a+1) w)-
      (5/8:ℂ)*(complexSample (a+1) w-complexSample a w) := by
    unfold complexBoundary tailBoundary
    ring
  have h0 := complex_first_bound a ha w hw
  have h1 := complex_first_bound (a+1) (by omega) w hw
  rw [show a+1+1=a+2 by omega] at h1
  have hb : 1/((a+1:ℕ):ℝ) ≤ 1/(a:ℝ) :=
    one_div_le_one_div_of_le (by exact_mod_cast ha) (by push_cast; linarith)
  rw [he]
  have h := norm_sub_le ((3/8:ℂ)*(complexSample (a+2) w-complexSample (a+1) w))
    ((5/8:ℂ)*(complexSample (a+1) w-complexSample a w))
  norm_num [norm_mul] at h
  apply h.trans
  calc
    _ ≤ (3/8:ℝ)*(1/(a:ℝ))+(5/8:ℝ)*(1/(a:ℝ)) := by gcongr; exact h1.trans hb
    _ = 1/(a:ℝ) := by ring

theorem complex_remainder_bound (a : ℕ) (ha : 0 < a) (w : ℂ) (hw : ‖w‖ ≤ (1/2:ℝ)) :
    ‖complexRemainder a w‖ ≤ 30/(a:ℝ)^4 := by
  have h0 := complex_fourth_bound a ha w hw
  have h1 := complex_fourth_bound (a+1) (by omega) w hw
  have h2 := complex_fourth_bound (a+2) (by omega) w hw
  have hb (j : ℕ) : 24/((a+j:ℕ):ℝ)^4 ≤ 24/(a:ℝ)^4 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    gcongr
    simp
  unfold complexRemainder tailRemainder
  have h := (norm_add_le
    ((3/8:ℂ)*complexFourth a w+(1/2:ℂ)*complexFourth (a+1) w)
    ((3/8:ℂ)*complexFourth (a+2) w)).trans (add_le_add (norm_add_le _ _) (le_refl _))
  norm_num [norm_mul] at h
  apply h.trans
  calc
    _ ≤ (3/8:ℝ)*(24/(a:ℝ)^4)+(1/2:ℝ)*(24/(a:ℝ)^4)+(3/8:ℝ)*(24/(a:ℝ)^4) := by
      gcongr
      · exact h1.trans (hb 1)
      · exact h2.trans (hb 2)
    _ = 30/(a:ℝ)^4 := by ring

/-- Cauchy estimate on normalized jets, with the same fixed circle as #59. -/
theorem normalized_cauchy_half (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (C : ℝ) (hb : ∀ w, ‖w‖ ≤ (1/2:ℝ) → ‖f w‖ ≤ C) (m : ℕ) :
    ‖complexJet m f‖ ≤ C*2^m := by
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    (c:=(0:ℂ)) (f:=f) m (by norm_num : (0:ℝ) < 1/2) hf.diffContOnCl (by
      intro w hw
      apply hb w
      exact (show ‖w‖ = (1/2:ℝ) by simpa only [Metric.mem_sphere, dist_zero_right] using hw).le)
  rw [complexJet, norm_div, Complex.norm_natCast]
  apply (div_le_iff₀ (by positivity : (0:ℝ) < m.factorial)).2
  rw [show (1/2:ℝ)^m = (2^m)⁻¹ by rw [one_div, inv_pow], div_inv_eq_mul] at h
  have he : C*2^m*(m.factorial:ℝ) = m.factorial*C*2^m := by ring
  rw [he]
  exact h

def nativeBoundary (a : ℕ) (t : ℝ) : ℂ := tailBoundary (criticalMaterialSample t) a
def nativeRemainder (a : ℕ) (t : ℝ) : ℂ := tailRemainder (criticalMaterialSample t) a
def nativeFourth (a : ℕ) (t : ℝ) : ℂ := delta4 (criticalMaterialSample t) a

theorem complex_fourth_real (a : ℕ) (ha : 0 < a) (t : ℝ) :
    complexFourth a (t:ℂ) = nativeFourth a t := by
  simp only [complexFourth, nativeFourth, delta4]
  rw [complex_sample_real _ (by omega), complex_sample_real _ (by omega),
    complex_sample_real _ (by omega), complex_sample_real _ (by omega), complex_sample_real a ha]

theorem complex_boundary_real (a : ℕ) (ha : 0 < a) (t : ℝ) :
    complexBoundary a (t:ℂ) = nativeBoundary a t := by
  simp only [complexBoundary, nativeBoundary, tailBoundary]
  rw [complex_sample_real _ (by omega), complex_sample_real _ (by omega), complex_sample_real a ha]

theorem complex_remainder_real (a : ℕ) (ha : 0 < a) (t : ℝ) :
    complexRemainder a (t:ℂ) = nativeRemainder a t := by
  change (3/8:ℂ)*complexFourth a (t:ℂ)+(1/2:ℂ)*complexFourth (a+1) (t:ℂ)+
    (3/8:ℂ)*complexFourth (a+2) (t:ℂ) = _
  rw [complex_fourth_real a ha, complex_fourth_real _ (by omega), complex_fourth_real _ (by omega)]
  rfl

theorem native_boundary_analytic (a : ℕ) (ha : 0 < a) : AnalyticAt ℝ (nativeBoundary a) 0 := by
  have hc : AnalyticAt ℂ (complexBoundary a) (0:ℂ) := (complex_boundary_entire a ha).analyticAt 0
  have h := AnalyticAt.comp_of_eq (g:=complexBoundary a) (f:=fun t : ℝ => (t:ℂ))
    (x:=(0:ℝ)) (hc.restrictScalars (𝕜:=ℝ)) (Complex.ofRealCLM.analyticAt (0:ℝ)) rfl
  simpa only [Function.comp_def, Complex.ofRealCLM_apply, complex_boundary_real a ha] using h

theorem native_remainder_analytic (a : ℕ) (ha : 0 < a) : AnalyticAt ℝ (nativeRemainder a) 0 := by
  have hc : AnalyticAt ℂ (complexRemainder a) (0:ℂ) := (complex_remainder_entire a ha).analyticAt 0
  have h := AnalyticAt.comp_of_eq (g:=complexRemainder a) (f:=fun t : ℝ => (t:ℂ))
    (x:=(0:ℝ)) (hc.restrictScalars (𝕜:=ℝ)) (Complex.ofRealCLM.analyticAt (0:ℝ)) rfl
  simpa only [Function.comp_def, Complex.ofRealCLM_apply, complex_remainder_real a ha] using h

def fourthJet (m a : ℕ) : ℂ := rJet m (nativeFourth a)
def boundaryJet (m a : ℕ) : ℂ := rJet m (nativeBoundary a)
def remainderJet (m a : ℕ) : ℂ := rJet m (nativeRemainder a)

theorem fourth_jet_bound (m a : ℕ) (ha : 0 < a) :
    ‖fourthJet m a‖ ≤ 24*2^m/(a:ℝ)^4 := by
  rw [fourthJet, rJet, real_jet_complex (.of_forall (fun t => (complex_fourth_real a ha t).symm))
    ((complex_fourth_entire a ha).analyticAt 0)]
  simpa only [div_mul_eq_mul_div] using normalized_cauchy_half _ (complex_fourth_entire a ha)
    _ (fun w hw => complex_fourth_bound a ha w hw) m

theorem boundary_jet_bound (m a : ℕ) (ha : 0 < a) :
    ‖boundaryJet m a‖ ≤ 2^m/(a:ℝ) := by
  rw [boundaryJet, rJet, real_jet_complex (.of_forall (fun t => (complex_boundary_real a ha t).symm))
    ((complex_boundary_entire a ha).analyticAt 0)]
  simpa only [one_div_mul_eq_div] using normalized_cauchy_half _ (complex_boundary_entire a ha)
    _ (fun w hw => complex_boundary_bound a ha w hw) m

theorem remainder_jet_bound (m a : ℕ) (ha : 0 < a) :
    ‖remainderJet m a‖ ≤ 30*2^m/(a:ℝ)^4 := by
  rw [remainderJet, rJet, real_jet_complex (.of_forall (fun t => (complex_remainder_real a ha t).symm))
    ((complex_remainder_entire a ha).analyticAt 0)]
  simpa only [div_mul_eq_mul_div] using normalized_cauchy_half _ (complex_remainder_entire a ha)
    _ (fun w hw => complex_remainder_bound a ha w hw) m
end
end CarryFourthTail
