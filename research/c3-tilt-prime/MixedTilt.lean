import CriticalTiltSlice

namespace CarryTiltSlice
open CPFormal.Analytic.Cp CarrySelfAdjointOperator
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

def displacedParameter (d t : ℝ) : ℂ := (((1/2:ℝ)+d:ℝ):ℂ) + Complex.I*(t:ℂ)

theorem displacedParameter_re (d t : ℝ) : (displacedParameter d t).re = 1/2+d := by
  simp [displacedParameter]

theorem displacedParameter_im (d t : ℝ) : (displacedParameter d t).im = t := by
  simp [displacedParameter]

theorem criticalParameter_im (t : ℝ) : (criticalParameter t).im = t := by
  simp [criticalParameter]

theorem center_gt_one (k : ℕ) : (1:ℝ) < canonicalRealCpCenter k := by
  unfold canonicalRealCpCenter
  have hk : (1:ℝ) ≤ ((k+1:ℕ):ℝ) := by exact_mod_cast (show 1 ≤ k+1 by omega)
  nlinarith

theorem tilted_cell_displaced (k : ℕ) (d t : ℝ) :
    canonicalCriticalWeightedTiltBlock k (displacedParameter d t) =
      localCriticalLineCarrier (criticalParameter t) (canonicalRealCpCenter k) 0 *
        (cpTilt 3 d (canonicalRealCpCenter k):ℂ) := by
  have hrad : criticalDisplacement (displacedParameter d t).re = d := by
    rw [displacedParameter_re]
    simp [criticalDisplacement]
  unfold canonicalCriticalWeightedTiltBlock
  rw [hrad]
  congr 1
  unfold localCriticalLineCarrier criticalLineDirichletCarrier
  rw [displacedParameter_im,criticalParameter_im]

theorem tilt_cell_transverse_derivative (k : ℕ) (t : ℝ) :
    HasDerivAt (fun d : ℝ => canonicalCriticalWeightedTiltBlock k (displacedParameter d t))
      (localCriticalLineCarrier (criticalParameter t) (canonicalRealCpCenter k) 0 *
        (carryTiltThreeFirstSensitivity (canonicalRealCpCenter k):ℂ)) 0 := by
  have he : (fun d : ℝ => canonicalCriticalWeightedTiltBlock k (displacedParameter d t)) =
      (fun d : ℝ => localCriticalLineCarrier (criticalParameter t) (canonicalRealCpCenter k) 0 *
        (cpTilt 3 d (canonicalRealCpCenter k):ℂ)) := by
    funext d
    exact tilted_cell_displaced k d t
  rw [he]
  exact (hasDerivAt_cpTilt_three_zero (center_gt_one k)).ofReal_comp.const_mul _

#print axioms tilt_cell_transverse_derivative

end
end CarryTiltSlice
