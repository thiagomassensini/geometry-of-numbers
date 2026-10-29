import ShiftedFalling
import EulerNewtonBridge

namespace CarryEulerNewtonAll
open CarrySelfAdjointOperator CarryNativeBinomial CarrySelfAdjointOperator.ChiralReturn
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- Raw-input expression for the existing scaled Euler boundary chart.
Its physical identification is proved separately with the original amplitude. -/
def eulerChart (N : ℕ) (t : ℝ) (x : Fin N → ℂ) (j : Fin N) : ℂ :=
  (t:ℂ)^(j:ℕ)*∑ r : Fin N, x r/(Real.sqrt 2:ℂ)*((r:ℂ)+1)^(j:ℕ)

/-- The general Euler-Newton matrix. Coefficients above the diagonal vanish
by degree, so every entry is polynomial in t, including at t=0. -/
def eulerNewtonMatrix (N : ℕ) (t : ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  fun m j => (Real.sqrt 2:ℂ)*nativeSourceJetOrderPhase m*Complex.I^(m:ℕ)*
    (shiftedFalling m).coeff j*(t:ℂ)^((m:ℕ)-(j:ℕ))

def eulerNewton (N : ℕ) (t : ℝ) (v : Fin N → ℂ) : Fin N → ℂ :=
  (eulerNewtonMatrix N t).mulVec v

theorem euler_newton_above (N : ℕ) (t : ℝ) (m j : Fin N) (h : (m:ℕ) < (j:ℕ)) :
    eulerNewtonMatrix N t m j=0 := by
  simp [eulerNewtonMatrix, shifted_falling_above m j h]

theorem euler_newton_address (N : ℕ) (t : ℝ) (x : Fin N → ℂ) (m : Fin N) :
    eulerNewton N t (eulerChart N t x) m=
      nativeSourceJetOrderPhase m*Complex.I^(m:ℕ)*(t:ℂ)^(m:ℕ)*
        ((m:ℕ).factorial:ℂ)*(∑ r : Fin N, (Nat.choose (r:ℕ) (m:ℕ):ℂ)*x r) := by
  have hs : (Real.sqrt 2:ℂ)≠0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)).ne'
  have hterm (j r : Fin N) :
      eulerNewtonMatrix N t m j*((t:ℂ)^(j:ℕ)*
        (x r/(Real.sqrt 2:ℂ)*((r:ℂ)+1)^(j:ℕ)))=
      nativeSourceJetOrderPhase m*Complex.I^(m:ℕ)*
        ((shiftedFalling m).coeff j*(t:ℂ)^((m:ℕ)-(j:ℕ))*
          ((t:ℂ)*((r:ℂ)+1))^(j:ℕ))*x r := by
    unfold eulerNewtonMatrix
    rw [mul_pow]
    field_simp [hs]
  unfold eulerNewton eulerChart
  simp only [Matrix.mulVec, dotProduct]
  simp_rw [Finset.mul_sum, hterm]
  rw [Finset.sum_comm]
  calc
    _ = ∑ r : Fin N, (nativeSourceJetOrderPhase m*Complex.I^(m:ℕ))*
        ((t:ℂ)^(m:ℕ)*(shiftedFalling m).eval ((r:ℂ)+1))*x r := by
      apply Finset.sum_congr rfl
      intro r _
      rw [← Finset.sum_mul, ← Finset.mul_sum,
        shifted_falling_scaled_eval N m m.isLt]
    _ = _ := by
      simp_rw [shifted_falling_address]
      apply Finset.sum_congr rfl
      intro r _
      ring

/-- The concrete source diagram, with the prescribed imaginary step. -/
theorem euler_newton_raw_exact (n k : ℕ) (x : Fin (2*n) → ℂ) :
    eulerNewton (2*n) (radialFourSourceStep k)
      (eulerChart (2*n) (radialFourSourceStep k) x)=newtonCoordinates n k x := by
  funext m
  rw [euler_newton_address]
  unfold newtonCoordinates
  simp only [canonicalCompletedC3RadialSecondStep,
    canonicalGreenJetStep_eq_radialFourSourceStep, mul_pow]
  ring

theorem euler_newton_at_zero (N : ℕ) (v : Fin N → ℂ) :
    eulerNewton N 0 v=fun m : Fin N =>
      (Real.sqrt 2:ℂ)*nativeSourceJetOrderPhase m*Complex.I^(m:ℕ)*v m := by
  classical
  funext m
  unfold eulerNewton
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single m]
  · simp [eulerNewtonMatrix, shifted_falling_diagonal]
  · intro j _ hj
    by_cases h : (m:ℕ) < (j:ℕ)
    · rw [euler_newton_above N 0 m j h, zero_mul]
    · have hne : (m:ℕ)≠(j:ℕ) := by
        intro he; exact hj (Fin.ext he.symm)
      have hp : (m:ℕ)-(j:ℕ)≠0 := by omega
      simp [eulerNewtonMatrix, zero_pow hp]
  · simp

end
end CarryEulerNewtonAll
