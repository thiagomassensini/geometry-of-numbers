import Nonclosability

/-! Positive control in the PRE-EXISTING native vertical tower. It is not
identified with the norm of the synthesized nonorthogonal Cauchy columns. -/
namespace CarryMellinDomain
open CarrySourcePrime CarrySelfAdjointOperator CPFormal.Analytic.Cp
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

/-- The original profile is a bounded functional on its original tower. -/
def verticalReadout (p : ℕ) : NativeGpreTowerHilbert →L[ℝ] ℝ :=
  innerSL ℝ (nativeGpreTowerProfileVector p 1)

theorem vertical_readout_finite_source {N : ℕ} (c : Fin (N+1) → ℝ) (p : ℕ) :
    verticalReadout p (finiteTowerSynthesis c)=
      ∫ u in (0:ℝ)..(p:ℝ)⁻¹, mellinTailPolynomial c u :=
  (mellin_integral_native_profile c p).symm

/-- An independently proved geometric profile bound controls every source. -/
theorem vertical_readout_norm_bound (p : ℕ) (hp : 2≤p) (X : NativeGpreTowerHilbert) :
    |verticalReadout p X|^2≤(((p:ℝ)^2-1)⁻¹)*‖X‖^2 := by
  have hcs := abs_real_inner_le_norm (nativeGpreTowerProfileVector p 1) X
  have hs := (sq_le_sq₀ (abs_nonneg _)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 hcs
  rw [sq_abs,mul_pow] at hs
  have hpbound := nativeGpreTowerProfileVector_one_norm_sq_le_resolvent p hp
  change |inner ℝ (nativeGpreTowerProfileVector p 1) X|^2≤_
  rw [sq_abs]
  exact hs.trans (mul_le_mul_of_nonneg_right hpbound (sq_nonneg _))

theorem finite_tower_coordinate {N : ℕ} (c : Fin (N+1) → ℝ) (i : Fin (N+1)) :
    finiteTowerSynthesis c i.val=c i := by
  classical
  simp only [finiteTowerSynthesis,lp.coeFn_sum,Finset.sum_apply,lp.coeFn_smul,
    Pi.smul_apply,smul_eq_mul,towerBasis,lp.single_apply]
  simp [Pi.single_apply,← Fin.ext_iff]

/-- The very same witnesses DO NOT become small in the original tower norm. -/
theorem concentrating_vertical_coordinate (n : ℕ) :
    finiteTowerSynthesis (concentratingCoefficients n) 1=(n:ℝ)+1 := by
  let j : Fin (n+1) := ⟨0,by omega⟩
  have h := finite_tower_coordinate (concentratingCoefficients n) j.succ
  change finiteTowerSynthesis (concentratingCoefficients n) 1=concentratingCoefficients n j.succ at h
  rw [h]
  have hc : boundaryCoefficients n j.succ=(-1:ℝ)^j.val*(n.choose j.val:ℝ) := Fin.cases_succ j
  change ((n:ℝ)+1)*boundaryCoefficients n j.succ=(n:ℝ)+1
  rw [hc]
  simp [j]

theorem concentrating_vertical_norm_ge (n : ℕ) :
    (n:ℝ)+1≤‖finiteTowerSynthesis (concentratingCoefficients n)‖ := by
  have h := lp.norm_apply_le_norm (by norm_num : (2:ENNReal)≠0)
    (finiteTowerSynthesis (concentratingCoefficients n)) 1
  rw [concentrating_vertical_coordinate] at h
  simpa only [Real.norm_eq_abs,abs_of_pos (show (0:ℝ)<(n:ℝ)+1 by positivity)] using h

/-- The vertical data cannot be recovered by a bounded map from the Cauchy
norm alone. This says nothing against starting with the original vertical data. -/
theorem no_continuous_vertical_recovery
    (R : CanonicalCompletedNativeChiralCauchyCarrier →L[ℝ] NativeGpreTowerHilbert)
    (hR : ∀ (N : ℕ) (c : Fin (N+1) → ℝ), c 0=0 →
      R (ContinuousMap.toLp 2 MeasureTheory.volume ℂ (originalContinuousSynthesis c))=
        finiteTowerSynthesis c) : False := by
  apply no_continuous_mellin_extension primeTwo ((verticalReadout 2).comp R)
  intro z hz
  obtain ⟨N,c,hc,hz⟩ := hz
  subst z
  change verticalReadout 2 (R (ContinuousMap.toLp 2 MeasureTheory.volume ℂ
    (originalContinuousSynthesis c)))=_
  rw [hR N c hc,vertical_readout_finite_source]
  rfl

end
end CarryMellinDomain
