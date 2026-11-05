import SigmaNativeZeroBridge
import HardyFirstZero.FirstZero

/-!
# Certified finite negative direction for every small noncentral shift

The only external mathematical input is the kernel-checked first positive
critical-line zero. Its zeta value is transported to the original completed
native characteristic inside the genuine critical strip, then fed to the
already-proved conditional obstruction for the original `sigmaMatrix`.
-/

namespace CarrySigmaObstruction

open CarrySelfAdjointOperator CarryMovingSigma CPFormal.Analytic.Cp
open scoped BigOperators Matrix

noncomputable section
set_option autoImplicit false

/-- The critical-line point at positive ordinate `t`. -/
def sigmaLineZero (t : ℝ) : ℂ := (1 / 2 : ℂ) + (t : ℂ) * Complex.I

/-- Every nonzero shift of size below `1/4` has a finite negative direction
for the original sigma Hankel matrix. -/
theorem certified_sigma_negative_direction_of_nonzero_small_shift
    (d : ℝ) (hd₀ : 0 < |d|) (hd₁ : |d| < (1 / 4 : ℝ)) :
    ∃ N : ℕ, ∃ v : Fin N → ℝ, v ≠ 0 ∧
      v ⬝ᵥ (sigmaMatrix d 0 N *ᵥ v) < 0 := by
  obtain ⟨γ, hγbox, hline⟩ := HardyFirstZero.first_zero_on_line
  have hγ : 0 < γ := by
    exact lt_trans (by norm_num : (0 : ℝ) < 1413 / 100) hγbox.1
  have hparam : operatorHeightParameter (γ : ℂ) = sigmaLineZero γ := by
    simp [sigmaLineZero, CarrySelfAdjointOperator.operatorHeightParameter]
    ring
  have hζγ : riemannZeta (operatorHeightParameter (γ : ℂ)) = 0 := by
    rw [hparam]
    simpa [sigmaLineZero] using hline
  have hsγ : operatorHeightParameter (γ : ℂ) ∈ genuineCriticalStrip := by
    norm_num [genuineCriticalStrip, CarrySelfAdjointOperator.operatorHeightParameter]
  have hcontinuation : completedNativeCharacteristicContinuation (γ : ℂ) = 0 :=
    (completedNativeCharacteristicContinuation_zero_iff_zeta hsγ).2 hζγ
  have hzero : completedNativeOperatorCharacteristic (γ : ℂ) = 0 := by
    rw [← completedNativeCharacteristicContinuation_eq_native hsγ]
    exact hcontinuation
  exact exists_sigmaMatrix_negative_direction_of_zero d γ hγ hd₀ hd₁ hzero

end
end CarrySigmaObstruction

#print axioms CarrySigmaObstruction.certified_sigma_negative_direction_of_nonzero_small_shift
#print axioms HardyFirstZero.first_zero_on_line
