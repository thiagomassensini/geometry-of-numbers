import CenteredLogRecurrence
import ResidualObstructions

/-! Conditional relative error budgets and a finite counterexample to an
absolute-error-only sign argument. The proxy is not the Carry source. -/
namespace CarryRelativeResidual
open CarrySelfAdjointOperator CarryCriticalSource CarryVariationalSchur
open scoped BigOperators Matrix
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000

/-- A relative budget supplies the strict residual criterion. Coercivity
and the trial energy must be independently established at this order. -/
theorem schur_pos_of_relative_budget (m : ℕ → ℝ) (s n : ℕ)
    (hA : (sourceMomentMatrix m s n).PosDef) (α η : ℝ)
    (hα : 0 < α) (hη : η < 1)
    (hcoerc : ∀ y : Fin n → ℝ,
      α*(y ⬝ᵥ y) ≤ sourceMomentQuadratic m s n y)
    (z : Fin n → ℝ) (hE : 0 < sourceTrialEnergy m s n z)
    (hrel : sourceTrialResidual m s n z ⬝ᵥ sourceTrialResidual m s n z ≤
      η*(α*sourceTrialEnergy m s n z)) :
    0 < sourceMomentSchur m s n := by
  apply sourceMomentSchur_pos_of_trialResidual m s n hA α hα hcoerc z
  apply lt_of_le_of_lt hrel
  simpa only [one_mul] using mul_lt_mul_of_pos_right hη (mul_pos hα hE)

def perturbedMoments (δ : ℝ) (k : ℕ) : ℝ := if k=2 then 1+δ else 1

theorem perturbed_old_prefix (δ : ℝ) :
    sourceMomentMatrix (perturbedMoments δ) 0 1 = 1 := by
  ext i j
  fin_cases i
  fin_cases j
  norm_num [sourceMomentMatrix,perturbedMoments]

theorem perturbed_schur (δ : ℝ) :
    sourceMomentSchur (perturbedMoments δ) 0 1 = δ := by
  rw [CarryResidualObstructions.schur_one_formula]
  norm_num [perturbedMoments]

/-- Arbitrarily close finite moment data, with the same positive old
prefix, can have opposite next signs. This is not a native counterexample. -/
theorem absolute_closeness_opposite_signs (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ 2*δ < ε ∧
      (∀ k, |perturbedMoments δ k-perturbedMoments (-δ) k| ≤ 2*δ) ∧
      0 < sourceMomentSchur (perturbedMoments δ) 0 1 ∧
      sourceMomentSchur (perturbedMoments (-δ)) 0 1 < 0 := by
  refine ⟨ε/4,by positivity,by linarith,?_,?_,?_⟩
  · intro k
    unfold perturbedMoments
    split_ifs
    · rw [abs_of_nonneg (by linarith : 0 ≤ 1+ε/4-(1+-(ε/4)))]
      linarith
    · simp only [sub_self,abs_zero]
      positivity
  · rw [perturbed_schur]
    positivity
  · rw [perturbed_schur]
    linarith

end
end CarryRelativeResidual
