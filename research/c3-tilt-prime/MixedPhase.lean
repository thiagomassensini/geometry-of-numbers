import MixedTilt

namespace CarryTiltSlice
open CPFormal.Analytic.Cp CarrySelfAdjointOperator
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

theorem critical_carrier_phase (k : ℕ) (t : ℝ) :
    localCriticalLineCarrier (criticalParameter t) (canonicalRealCpCenter k) 0 =
      ((canonicalRealCpCenter k ^ (-(1/2:ℝ)):ℝ):ℂ) *
        Complex.exp ((-Complex.I*(Real.log (canonicalRealCpCenter k):ℂ))*(t:ℂ)) := by
  let c : ℝ := canonicalRealCpCenter k
  have hc : 0 < c := lt_trans zero_lt_one (center_gt_one k)
  have hn : (c:ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hc)
  unfold localCriticalLineCarrier criticalLineDirichletCarrier
  rw [criticalParameter_im]
  simp only [Int.cast_zero, add_zero]
  change (c:ℂ)^(-(1/2+Complex.I*(t:ℂ))) = _
  rw [show (-(1/2+Complex.I*(t:ℂ)):ℂ) = -(1/2:ℂ)+(-Complex.I*(t:ℂ)) by ring]
  rw [Complex.cpow_add _ _ hn]
  have hp := (Complex.ofReal_cpow hc.le (-(1/2:ℝ))).symm
  push_cast at hp
  rw [hp,Complex.cpow_def_of_ne_zero hn,← Complex.ofReal_log hc.le]
  congr 1
  congr 1
  ring

def mixedTiltWave (k : ℕ) (z : ℂ) : ℂ :=
  ((canonicalRealCpCenter k ^ (-(1/2:ℝ)) *
      carryTiltThreeFirstSensitivity (canonicalRealCpCenter k):ℝ):ℂ) *
    Complex.exp ((-Complex.I*(Real.log (canonicalRealCpCenter k):ℂ))*z)

theorem mixed_tilt_wave_of_real (k : ℕ) (t : ℝ) :
    deriv (fun d : ℝ => canonicalCriticalWeightedTiltBlock k (displacedParameter d t)) 0 =
      mixedTiltWave k (t:ℂ) := by
  rw [(tilt_cell_transverse_derivative k t).deriv,critical_carrier_phase]
  unfold mixedTiltWave
  push_cast
  ring

#print axioms critical_carrier_phase
#print axioms mixed_tilt_wave_of_real
end
end CarryTiltSlice
