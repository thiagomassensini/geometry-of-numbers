import CorrelatedJets17

namespace C3ShiftedFourth

open CarryC3Boxes CarryC3Tail CarryC3Gamma CarrySelfAdjointOperator
  PhysicalSewing CarryTwoEvenJets C3CofactorCorrelation
open Set Filter Topology
open scoped BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 30000000
set_option maxRecDepth 30000

def gammaReferenceCrosswalk17 (r : ℕ) : ℚ :=
  if hr : r < 13 then gammaRealReference13 ⟨r, hr⟩
  else if hr : r < 17 then gammaRealReference17 ⟨r, hr⟩ else 0

theorem gamma_reference_center_difference13 (r : Fin 13) :
    |gammaRealReference17 ⟨r.val, by omega⟩ - gammaRealReference13 r| ≤
      (1/10^30:ℚ) := by
  fin_cases r <;> decide +kernel

theorem native_gamma_crosswalk_boxes (r : Fin 17) :
    ‖sourceJet r.val nativeGamma - Complex.I^r.val *
      (gammaReferenceCrosswalk17 r.val:ℂ)‖ ≤
        2*4^r.val/10^34+(2/10^29:ℝ) := by
  by_cases hl : r.val < 13
  · let q : Fin 13 := ⟨r.val, hl⟩
    have hnew := native_gamma_seventeen_boxes r
    have hdelta : |(gammaRealReference17 r : ℝ) -
        (gammaRealReference13 q : ℝ)| ≤ (1/10^30:ℝ) := by
      have hd := gamma_reference_center_difference13 q
      simpa [q] using rat_abs_cast_le hd
    have hshift : ‖Complex.I^r.val *
        (((gammaRealReference17 r : ℝ) - (gammaRealReference13 q : ℝ)):ℂ)‖ ≤
          (1/10^30:ℝ) := by
      rw [norm_mul]
      have hI : ‖Complex.I^r.val‖ = 1 := by
        rw [norm_pow, Complex.norm_I, one_pow]
      rw [hI, one_mul]
      rw [← Complex.ofReal_sub]
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact hdelta
    have heq : sourceJet r.val nativeGamma - Complex.I^r.val *
        (gammaRealReference13 q:ℂ) =
          (sourceJet r.val nativeGamma - Complex.I^r.val *
            (gammaRealReference17 r:ℂ)) +
            Complex.I^r.val *
              (((gammaRealReference17 r:ℝ) - (gammaRealReference13 q:ℝ)):ℂ) := by
      push_cast
      ring
    have hcross : gammaReferenceCrosswalk17 r.val = gammaRealReference13 q := by
      simp [gammaReferenceCrosswalk17, q, hl]
    rw [hcross, heq]
    calc
      _ ≤ ‖sourceJet r.val nativeGamma - Complex.I^r.val *
            (gammaRealReference17 r:ℂ)‖ +
          ‖Complex.I^r.val *
            (((gammaRealReference17 r:ℝ) - (gammaRealReference13 q:ℝ)):ℂ)‖ :=
        norm_add_le _ _
      _ ≤ (2*4^r.val/10^34+(1/10^29:ℝ))+(1/10^30:ℝ) :=
        add_le_add hnew hshift
      _ ≤ 2*4^r.val/10^34+(2/10^29:ℝ) := by
        have hc : (1:ℝ)/10^29 + 1/10^30 ≤ 2/10^29 := by norm_num
        linarith
  · have hcross : gammaReferenceCrosswalk17 r.val = gammaRealReference17 r := by
      simp [gammaReferenceCrosswalk17, hl, r.isLt]
    rw [hcross]
    have h := native_gamma_seventeen_boxes r
    exact h.trans (by norm_num)



end
end C3ShiftedFourth
