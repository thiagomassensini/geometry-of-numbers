import GeometryOfNumbers.Analysis.BaseTwoCanonicalArchimedeanDressing
import GeometryOfNumbers.Analysis.BaseTwoSynthesizedClockMoments
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Data.Nat.Choose.Cast

/-! Concrete downstream dressing of the already-synthesized material signal.
Formal response = normalized all-order jets of the dressed function.
No Gram, Hankel positivity, Jacobi or height premise is used. -/
noncomputable section
open scoped BigOperators
namespace GeometryOfNumbers.Analysis.BaseTwoCompletion

private def normalizedSeries (f : ℝ → ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (fun r => (r.factorial:ℂ)⁻¹ * iteratedDeriv r f 0)

private theorem normalizedSeries_mul (f g : ℝ → ℂ)
    (hf : ContDiffAt ℝ ⊤ f 0) (hg : ContDiffAt ℝ ⊤ g 0) :
    normalizedSeries (f*g) = normalizedSeries f * normalizedSeries g := by
  apply PowerSeries.ext
  intro r
  simp only [normalizedSeries, PowerSeries.coeff_mk, PowerSeries.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    iteratedDeriv_mul (hf.of_le (by simp)) (hg.of_le (by simp)), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjr : j ≤ r := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  rw [Nat.cast_choose ℂ hjr]
  have hr : (r.factorial:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
  have hj : (j.factorial:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have hsub : ((r-j).factorial:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (r-j)
  field_simp

private theorem normalizedSeries_one : normalizedSeries (fun _ => (1:ℂ)) = 1 := by
  apply PowerSeries.ext
  intro r
  by_cases hr : r = 0 <;> simp [normalizedSeries, iteratedDeriv_const, hr]

private theorem normalizedSeries_camera_inverse :
    normalizedSeries (fun t => (baseTwoCanonicalCameraFactor t)⁻¹) =
      baseTwoCanonicalCameraFactorSeries⁻¹ := by
  apply (PowerSeries.eq_inv_iff_mul_eq_one baseTwoCanonicalCameraFactorSeries_constantCoeff_ne_zero).mpr
  have hc := baseTwoCanonicalCameraFactor_contDiff.contDiffAt (x:=0)
  have hm := normalizedSeries_mul (fun t => (baseTwoCanonicalCameraFactor t)⁻¹)
    baseTwoCanonicalCameraFactor (hc.inv (baseTwoCanonicalCameraFactor_ne_zero 0)) hc
  have he : (fun t => (baseTwoCanonicalCameraFactor t)⁻¹) * baseTwoCanonicalCameraFactor =
      (fun _ => (1:ℂ)) := by
    funext t
    exact inv_mul_cancel₀ (baseTwoCanonicalCameraFactor_ne_zero t)
  rw [he, normalizedSeries_one] at hm
  exact hm.symm

/-- Apply dressing to the complete function, not a partial head. -/
def baseTwoCanonicalResponse (t : ℝ) : ℂ :=
  canonicalArchimedeanCompletion t *
    (baseTwoCriticalCompleteSignal t * (baseTwoCanonicalCameraFactor t)⁻¹)

def baseTwoCanonicalResponseSeries : PowerSeries ℂ :=
  baseTwoSynthesizedResponseSeries baseTwoCanonicalCameraFactorSeries baseTwoCanonicalCompletionSeries

theorem baseTwoCanonicalResponse_analyticAt (t : ℝ) :
    AnalyticAt ℝ baseTwoCanonicalResponse t :=
  (canonicalArchimedeanCompletion_analyticAt t).mul
    ((baseTwoCriticalCompleteSignal_analyticAt t).mul
      ((baseTwoCanonicalCameraFactor_analyticAt t).inv (baseTwoCanonicalCameraFactor_ne_zero t)))

theorem baseTwoCanonicalResponseSeries_eq_normalizedJets :
    baseTwoCanonicalResponseSeries = PowerSeries.mk (fun r =>
      (r.factorial:ℂ)⁻¹ * iteratedDeriv r baseTwoCanonicalResponse 0) := by
  have hc := canonicalArchimedeanCompletion_contDiff.contDiffAt (x:=0)
  have hs := baseTwoCriticalCompleteSignal_contDiff.contDiffAt (x:=0)
  have hb := baseTwoCanonicalCameraFactor_contDiff.contDiffAt (x:=0)
  have hi := hb.inv (baseTwoCanonicalCameraFactor_ne_zero 0)
  have hinner := normalizedSeries_mul baseTwoCriticalCompleteSignal
    (fun t => (baseTwoCanonicalCameraFactor t)⁻¹) hs hi
  have houter := normalizedSeries_mul canonicalArchimedeanCompletion
    (baseTwoCriticalCompleteSignal * (fun t => (baseTwoCanonicalCameraFactor t)⁻¹)) hc (hs.mul hi)
  rw [hinner, normalizedSeries_camera_inverse] at houter
  exact houter.symm

theorem baseTwoCanonicalResponseSeries_coeff (r : ℕ) :
    PowerSeries.coeff r baseTwoCanonicalResponseSeries =
      (r.factorial:ℂ)⁻¹ * iteratedDeriv r baseTwoCanonicalResponse 0 := by
  rw [baseTwoCanonicalResponseSeries_eq_normalizedJets]
  exact PowerSeries.coeff_mk _ _

theorem baseTwoCanonicalClosedResponse_eq (M : ℕ) :
    baseTwoClosedResponseSeries M baseTwoCanonicalCameraFactorSeries baseTwoCanonicalCompletionSeries =
      baseTwoCanonicalResponseSeries :=
  baseTwoClosedResponseSeries_eq_synthesized M _ _

private theorem criticalSample_zero (n : ℕ) (hn : 0 < n) :
    criticalMaterialSample 0 n = (((n:ℝ)^(-1/2:ℝ):ℝ):ℂ) := by
  rw [criticalMaterialSample_eq_rpow_phase 0 hn]
  simp

private theorem inverseHalfPower_convex :
    ConvexOn ℝ (Set.Ioi 0) (fun x : ℝ => x^(-1/2:ℝ)) := by
  apply convexOn_of_deriv2_nonneg' (convex_Ioi 0)
  · intro x hx
    exact (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hx))).differentiableAt.differentiableWithinAt
  · rw [Real.deriv_rpow_const']
    intro x hx
    exact ((Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hx))).const_mul (-1/2:ℝ)).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [Function.iterate_succ_apply, Function.iterate_one, Real.deriv_rpow_const']
    rw [((Real.hasDerivAt_rpow_const (p:=(-1/2:ℝ)-1) (Or.inl (ne_of_gt hx))).const_mul (-1/2:ℝ)).deriv]
    have hp : 0 ≤ x^((-1/2:ℝ)-1-1) := Real.rpow_nonneg (le_of_lt hx) _
    nlinarith

/-- Nonnegative curvature of each complete cell at time zero. -/
theorem baseTwoCriticalCenterCell_zero_re_nonneg (k : ℕ) :
    0 ≤ (baseTwoCriticalCenterCell 0 k).re := by
  have hl : 0 < baseTwoLeftLeg k := by simp; omega
  have hc : 0 < baseTwoCenter k := by simp
  have hr : 0 < baseTwoRightLeg k := by simp
  have hm : (1/2:ℝ)*(baseTwoLeftLeg k:ℝ)+(1/2:ℝ)*(baseTwoRightLeg k:ℝ) = (baseTwoCenter k:ℝ) := by
    have h : baseTwoLeftLeg k + baseTwoRightLeg k = 2*baseTwoCenter k := by simp; omega
    have hreal : (baseTwoLeftLeg k:ℝ)+(baseTwoRightLeg k:ℝ)=2*(baseTwoCenter k:ℝ) := by exact_mod_cast h
    linarith
  have hconv := inverseHalfPower_convex.2
    (show (baseTwoLeftLeg k:ℝ) ∈ Set.Ioi 0 by simpa only [Set.mem_Ioi] using (show (0:ℝ) < (baseTwoLeftLeg k:ℝ) by exact_mod_cast hl))
    (show (baseTwoRightLeg k:ℝ) ∈ Set.Ioi 0 by simpa only [Set.mem_Ioi] using (show (0:ℝ) < (baseTwoRightLeg k:ℝ) by exact_mod_cast hr))
    (show (0:ℝ) ≤ 1/2 by norm_num) (show (0:ℝ) ≤ 1/2 by norm_num) (by norm_num)
  simp only [smul_eq_mul, hm] at hconv
  unfold baseTwoCriticalCenterCell
  rw [criticalSample_zero _ hl, criticalSample_zero _ hc, criticalSample_zero _ hr]
  norm_num only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  norm_num at hconv ⊢
  linarith

/-- The real center value retains the positive unit seed. -/
theorem baseTwoCriticalCompleteSignal_zero_re_pos :
    0 < (baseTwoCriticalCompleteSignal 0).re := by
  rw [baseTwoCriticalCompleteSignal, criticalMaterialSample_one, Complex.add_re,
    Complex.one_re, Complex.re_tsum (summable_baseTwoCriticalCenterCell 0)]
  have h : (0:ℝ) ≤ ∑' k : ℕ, (baseTwoCriticalCenterCell 0 k).re :=
    tsum_nonneg baseTwoCriticalCenterCell_zero_re_nonneg
  linarith

theorem baseTwoCriticalCompleteSignal_zero_im :
    (baseTwoCriticalCompleteSignal 0).im = 0 := by
  have hi : ∀ k, (baseTwoCriticalCenterCell 0 k).im = 0 := by
    intro k
    unfold baseTwoCriticalCenterCell
    rw [criticalSample_zero _ (by simp; omega), criticalSample_zero _ (by simp),
      criticalSample_zero _ (by simp)]
    simp
  rw [baseTwoCriticalCompleteSignal, criticalMaterialSample_one, Complex.add_im,
    Complex.one_im, Complex.im_tsum (summable_baseTwoCriticalCenterCell 0)]
  simp only [hi, tsum_zero, add_zero]

def baseTwoCanonicalPhi : ℕ → ℝ :=
  baseTwoSynthesizedPhi baseTwoCanonicalCameraFactorSeries baseTwoCanonicalCompletionSeries

def baseTwoCanonicalLogMoment : ℕ → ℝ :=
  baseTwoSynthesizedLogMoment baseTwoCanonicalCameraFactorSeries baseTwoCanonicalCompletionSeries

/-- Definitive candidate for the future Gram theorem, with no representation assumed. -/
def baseTwoCanonicalMomentSequence : ℕ → ℝ := baseTwoCanonicalLogMoment

theorem baseTwoCanonicalPhi_eq_synthesized :
    baseTwoCanonicalPhi = baseTwoSynthesizedPhi baseTwoCanonicalCameraFactorSeries baseTwoCanonicalCompletionSeries := rfl

theorem baseTwoCanonicalLogMoment_eq_synthesized :
    baseTwoCanonicalLogMoment = baseTwoSynthesizedLogMoment baseTwoCanonicalCameraFactorSeries baseTwoCanonicalCompletionSeries := rfl

theorem baseTwoCanonicalMomentSequence_eq_logMoment :
    baseTwoCanonicalMomentSequence = baseTwoCanonicalLogMoment := rfl

theorem baseTwoCanonicalPhi_eq_normalizedEvenJet (r : ℕ) :
    baseTwoCanonicalPhi r =
      (((2*r).factorial:ℂ)⁻¹ * iteratedDeriv (2*r) baseTwoCanonicalResponse 0).re := by
  change (PowerSeries.coeff (2*r) baseTwoCanonicalResponseSeries).re = _
  rw [baseTwoCanonicalResponseSeries_coeff]

theorem baseTwoCanonicalPhi_zero_pos : 0 < baseTwoCanonicalPhi 0 := by
  rw [baseTwoCanonicalPhi_eq_normalizedEvenJet]
  simp only [mul_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_mul, iteratedDeriv_zero]
  have hs : baseTwoCriticalCompleteSignal 0 = ((baseTwoCriticalCompleteSignal 0).re:ℂ) := by
    apply Complex.ext <;> simp [baseTwoCriticalCompleteSignal_zero_im]
  rw [baseTwoCanonicalResponse, hs, canonicalArchimedeanCompletion_zero,
    baseTwoCanonicalCameraFactor_zero]
  have he : ((-(1/8:ℝ)*Real.exp (-(Real.log Real.pi)/4)*Real.Gamma (1/4:ℝ):ℝ):ℂ) *
      (((baseTwoCriticalCompleteSignal 0).re:ℂ) * (-(((2:ℝ)^(-1/2:ℝ):ℝ):ℂ))⁻¹) =
    (((-(1/8:ℝ)*Real.exp (-(Real.log Real.pi)/4)*Real.Gamma (1/4:ℝ)) *
      ((baseTwoCriticalCompleteSignal 0).re * (-(2:ℝ)^(-1/2:ℝ))⁻¹):ℝ):ℂ) := by push_cast; rfl
  rw [he, Complex.ofReal_re]
  have hC : -(1/8:ℝ)*Real.exp (-(Real.log Real.pi)/4)*Real.Gamma (1/4:ℝ) < 0 := by
    have h := canonicalArchimedeanCompletion_zero_re_neg
    rwa [canonicalArchimedeanCompletion_zero, Complex.ofReal_re] at h
  have hB : -(2:ℝ)^(-1/2:ℝ) < 0 := neg_neg_of_pos (Real.rpow_pos_of_pos (by norm_num) _)
  exact mul_pos_of_neg_of_neg hC (mul_neg_of_pos_of_neg baseTwoCriticalCompleteSignal_zero_re_pos (inv_lt_zero.mpr hB))

theorem baseTwoCanonicalPhi_zero_ne_zero : baseTwoCanonicalPhi 0 ≠ 0 :=
  ne_of_gt baseTwoCanonicalPhi_zero_pos

theorem baseTwoCanonicalLogMoment_isSequence :
    IsLogDerivativeMomentSequence baseTwoCanonicalPhi baseTwoCanonicalLogMoment :=
  baseTwoSynthesizedLogMoment_isSequence _ _ baseTwoCanonicalPhi_zero_ne_zero

theorem baseTwoCanonicalLogMoment_unique (h : ℕ → ℝ)
    (hrel : IsLogDerivativeMomentSequence baseTwoCanonicalPhi h) :
    baseTwoCanonicalLogMoment = h :=
  baseTwoSynthesizedLogMoment_unique _ _ baseTwoCanonicalPhi_zero_ne_zero h hrel

theorem baseTwoCanonicalLogMoment_formal_logDerivative :
    PowerSeries.mk baseTwoCanonicalLogMoment * PowerSeries.mk baseTwoCanonicalPhi =
      -(PowerSeries.derivative ℝ (PowerSeries.mk baseTwoCanonicalPhi)) :=
  baseTwoSynthesizedLogMoment_formal_logDerivative _ _ baseTwoCanonicalPhi_zero_ne_zero

theorem baseTwoCanonicalLogMoment_unique_of_formal_identity (h : ℕ → ℝ)
    (hformal : PowerSeries.mk h * PowerSeries.mk baseTwoCanonicalPhi =
      -(PowerSeries.derivative ℝ (PowerSeries.mk baseTwoCanonicalPhi))) :
    baseTwoCanonicalLogMoment = h :=
  baseTwoSynthesizedLogMoment_unique_of_formal_identity _ _ baseTwoCanonicalPhi_zero_ne_zero h hformal

theorem baseTwoCanonicalLogMoment_cutoff_independent (M : ℕ) :
    baseTwoHistoricalLogMoment M baseTwoCanonicalCameraFactorSeries baseTwoCanonicalCompletionSeries =
      baseTwoCanonicalLogMoment :=
  baseTwoHistoricalLogMoment_eq_synthesized M _ _

end GeometryOfNumbers.Analysis.BaseTwoCompletion
