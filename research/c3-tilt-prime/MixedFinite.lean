import MixedPhaseJets

namespace CarryTiltSlice
open CPFormal.Analytic.Cp CarrySelfAdjointOperator
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem finite_tilt_transverse_wave (M : ℕ) (t : ℝ) :
    deriv (fun d : ℝ => finiteCanonicalCriticalWeightedTiltTrace M (displacedParameter d t)) 0 =
      ∑ k ∈ Finset.range M, mixedTiltWave k (t:ℂ) := by
  have hd : HasDerivAt (fun d : ℝ => finiteCanonicalCriticalWeightedTiltTrace M (displacedParameter d t))
      (∑ k ∈ Finset.range M, localCriticalLineCarrier (criticalParameter t) (canonicalRealCpCenter k) 0 *
        (carryTiltThreeFirstSensitivity (canonicalRealCpCenter k):ℂ)) 0 := by
    unfold finiteCanonicalCriticalWeightedTiltTrace
    exact HasDerivAt.fun_sum fun k _ => tilt_cell_transverse_derivative k t
  rw [hd.deriv]
  apply Finset.sum_congr rfl
  intro k _
  exact (tilt_cell_transverse_derivative k t).deriv.symm.trans (mixed_tilt_wave_of_real k t)

theorem finite_mixed_tilt_positive (M n : ℕ) (hM : 0 < M) :
    0 < ((-1:ℂ)^n * iteratedDeriv (2*n) (fun t : ℝ =>
      deriv (fun d : ℝ => finiteCanonicalCriticalWeightedTiltTrace M (displacedParameter d t)) 0) 0).re := by
  have hf : (fun t : ℝ => deriv (fun d : ℝ => finiteCanonicalCriticalWeightedTiltTrace M (displacedParameter d t)) 0) =
      (fun t : ℝ => ∑ k ∈ Finset.range M, mixedTiltWave k (t:ℂ)) := by
    funext t
    exact finite_tilt_transverse_wave M t
  rw [hf,iteratedDeriv_fun_sum]
  · simp only [Finset.mul_sum,Complex.re_sum]
    apply Finset.sum_pos'
    · intro k hk
      have h := signed_even_mixed_tilt_pos k n
      have hg : (fun u : ℝ => mixedTiltWave k (u:ℂ)) =
          (fun u : ℝ => deriv (fun d : ℝ => canonicalCriticalWeightedTiltBlock k (displacedParameter d u)) 0) := by
        funext u
        exact (mixed_tilt_wave_of_real k u).symm
      rw [hg]
      exact h.le
    · refine ⟨0,by simpa using hM,?_⟩
      have h := signed_even_mixed_tilt_pos 0 n
      have hg : (fun u : ℝ => mixedTiltWave 0 (u:ℂ)) =
          (fun u : ℝ => deriv (fun d : ℝ => canonicalCriticalWeightedTiltBlock 0 (displacedParameter d u)) 0) := by
        funext u
        exact (mixed_tilt_wave_of_real 0 u).symm
      rw [hg]
      exact h
  · intro k hk
    have hcast : ContDiff ℝ ⊤ (fun u : ℝ => (u:ℂ)) := Complex.ofRealCLM.contDiff
    have he : ContDiff ℝ ⊤ (fun u : ℝ => Complex.exp (tiltFrequency k*(u:ℂ))) :=
      Complex.contDiff_exp.comp (contDiff_const.mul hcast)
    have hm : ContDiff ℝ ⊤ (fun u : ℝ => mixedTiltWave k (u:ℂ)) := by
      unfold mixedTiltWave
      simpa only [tiltFrequency] using (contDiff_const.mul he)
    exact ((hm.of_le (by simp)).contDiffAt)

#print axioms finite_tilt_transverse_wave
#print axioms finite_mixed_tilt_positive
theorem finite_mixed_tilt_identity (M n : ℕ) :
    ((-1:ℂ)^n * iteratedDeriv (2*n) (fun t : ℝ =>
      deriv (fun d : ℝ => finiteCanonicalCriticalWeightedTiltTrace M (displacedParameter d t)) 0) 0).re =
      ∑ k ∈ Finset.range M,
        (canonicalRealCpCenter k ^ (-(1/2:ℝ)) *
          carryTiltThreeFirstSensitivity (canonicalRealCpCenter k)) *
            (Real.log (canonicalRealCpCenter k))^(2*n) := by
  have hf : (fun t : ℝ => deriv (fun d : ℝ => finiteCanonicalCriticalWeightedTiltTrace M (displacedParameter d t)) 0) =
      (fun t : ℝ => ∑ k ∈ Finset.range M, mixedTiltWave k (t:ℂ)) := by
    funext t
    exact finite_tilt_transverse_wave M t
  rw [hf,iteratedDeriv_fun_sum]
  · simp only [Finset.mul_sum,Complex.re_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hg : (fun u : ℝ => mixedTiltWave k (u:ℂ)) =
        (fun u : ℝ => deriv (fun d : ℝ => canonicalCriticalWeightedTiltBlock k (displacedParameter d u)) 0) := by
      funext u
      exact (mixed_tilt_wave_of_real k u).symm
    rw [hg]
    exact signed_even_mixed_tilt k n
  · intro k hk
    have hcast : ContDiff ℝ ⊤ (fun u : ℝ => (u:ℂ)) := Complex.ofRealCLM.contDiff
    have he : ContDiff ℝ ⊤ (fun u : ℝ => Complex.exp (tiltFrequency k*(u:ℂ))) :=
      Complex.contDiff_exp.comp (contDiff_const.mul hcast)
    have hm : ContDiff ℝ ⊤ (fun u : ℝ => mixedTiltWave k (u:ℂ)) := by
      unfold mixedTiltWave
      simpa only [tiltFrequency] using (contDiff_const.mul he)
    exact ((hm.of_le (by simp)).contDiffAt)

#print axioms finite_mixed_tilt_identity

end
end CarryTiltSlice
