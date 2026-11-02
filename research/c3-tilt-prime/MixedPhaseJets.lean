import MixedPhase

namespace CarryTiltSlice
open CPFormal.Analytic.Cp CarrySelfAdjointOperator
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

def tiltFrequency (k : ℕ) : ℂ := -Complex.I * (Real.log (canonicalRealCpCenter k):ℂ)

theorem mixedTiltWave_hasDerivAt (k : ℕ) (z : ℂ) :
    HasDerivAt (mixedTiltWave k) (tiltFrequency k * mixedTiltWave k z) z := by
  have hl : HasDerivAt (fun w : ℂ => tiltFrequency k*w) (tiltFrequency k) z := by
    simpa using (hasDerivAt_id z).const_mul (tiltFrequency k)
  have he : HasDerivAt (fun w : ℂ => Complex.exp (tiltFrequency k*w))
      (Complex.exp (tiltFrequency k*z)*tiltFrequency k) z := by
    simpa only [Function.comp_def] using (Complex.hasDerivAt_exp _).comp z hl
  have h := he.const_mul ((canonicalRealCpCenter k ^ (-(1/2:ℝ)) *
      carryTiltThreeFirstSensitivity (canonicalRealCpCenter k):ℝ):ℂ)
  change HasDerivAt (fun w : ℂ => ((canonicalRealCpCenter k ^ (-(1/2:ℝ)) *
      carryTiltThreeFirstSensitivity (canonicalRealCpCenter k):ℝ):ℂ) *
        Complex.exp (tiltFrequency k*w))
      (tiltFrequency k * (((canonicalRealCpCenter k ^ (-(1/2:ℝ)) *
        carryTiltThreeFirstSensitivity (canonicalRealCpCenter k):ℝ):ℂ) *
        Complex.exp (tiltFrequency k*z))) z
  convert h using 1 <;> (first | rfl | ring)

theorem mixedTiltWave_real_hasDerivAt (k : ℕ) (t : ℝ) :
    HasDerivAt (fun u : ℝ => mixedTiltWave k (u:ℂ))
      (tiltFrequency k * mixedTiltWave k (t:ℂ)) t := by
  exact (mixedTiltWave_hasDerivAt k (t:ℂ)).comp_ofReal

theorem mixedTiltWave_real_iterated (k n : ℕ) (t : ℝ) :
    iteratedDeriv n (fun u : ℝ => mixedTiltWave k (u:ℂ)) t =
      (tiltFrequency k)^n * mixedTiltWave k (t:ℂ) := by
  induction n generalizing t with
  | zero => simp
  | succ n ih =>
    have hf : iteratedDeriv n (fun u : ℝ => mixedTiltWave k (u:ℂ)) =
        (fun u : ℝ => (tiltFrequency k)^n * mixedTiltWave k (u:ℂ)) := by
      funext u
      exact ih u
    rw [iteratedDeriv_succ,hf]
    have hd := (mixedTiltWave_real_hasDerivAt k t).const_mul ((tiltFrequency k)^n)
    rw [hd.deriv]
    simp only [pow_succ]
    ring

theorem mixed_tilt_iterated (k n : ℕ) (t : ℝ) :
    iteratedDeriv n (fun u : ℝ =>
      deriv (fun d : ℝ => canonicalCriticalWeightedTiltBlock k (displacedParameter d u)) 0) t =
      (tiltFrequency k)^n * mixedTiltWave k (t:ℂ) := by
  have hf : (fun u : ℝ => deriv (fun d : ℝ => canonicalCriticalWeightedTiltBlock k (displacedParameter d u)) 0) =
      (fun u : ℝ => mixedTiltWave k (u:ℂ)) := by
    funext u
    exact mixed_tilt_wave_of_real k u
  rw [hf]
  exact mixedTiltWave_real_iterated k n t

#print axioms mixed_tilt_iterated
theorem tiltFrequency_sq (k : ℕ) :
    (tiltFrequency k)^2 = -((Real.log (canonicalRealCpCenter k):ℂ)^2) := by
  unfold tiltFrequency
  ring_nf
  simp [Complex.I_sq]

theorem signed_frequency_even (k n : ℕ) :
    (-1:ℂ)^n * (tiltFrequency k)^(2*n) =
      ((Real.log (canonicalRealCpCenter k):ℂ)^(2*n)) := by
  rw [pow_mul,tiltFrequency_sq,← mul_pow]
  have h : (-1:ℂ) * -((Real.log (canonicalRealCpCenter k):ℂ)^2) =
      (Real.log (canonicalRealCpCenter k):ℂ)^2 := by ring
  rw [h,← pow_mul]

theorem signed_even_mixed_tilt (k n : ℕ) :
    ((-1:ℂ)^n * iteratedDeriv (2*n) (fun u : ℝ =>
      deriv (fun d : ℝ => canonicalCriticalWeightedTiltBlock k (displacedParameter d u)) 0) 0).re =
      (canonicalRealCpCenter k ^ (-(1/2:ℝ)) *
        carryTiltThreeFirstSensitivity (canonicalRealCpCenter k)) *
          (Real.log (canonicalRealCpCenter k))^(2*n) := by
  rw [mixed_tilt_iterated]
  simp only [Complex.ofReal_zero,mixedTiltWave,mul_zero,Complex.exp_zero,mul_one]
  rw [← mul_assoc,signed_frequency_even]
  rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
  ring

theorem signed_even_mixed_tilt_pos (k n : ℕ) :
    0 < ((-1:ℂ)^n * iteratedDeriv (2*n) (fun u : ℝ =>
      deriv (fun d : ℝ => canonicalCriticalWeightedTiltBlock k (displacedParameter d u)) 0) 0).re := by
  rw [signed_even_mixed_tilt]
  have hc : 1 < canonicalRealCpCenter k := center_gt_one k
  have hl : 0 < Real.log (canonicalRealCpCenter k) := Real.log_pos hc
  exact mul_pos (mul_pos (Real.rpow_pos_of_pos (lt_trans zero_lt_one hc) _)
    (carryTiltThreeFirstSensitivity_pos hc)) (pow_pos hl _)

#print axioms signed_even_mixed_tilt
#print axioms signed_even_mixed_tilt_pos

end
end CarryTiltSlice
