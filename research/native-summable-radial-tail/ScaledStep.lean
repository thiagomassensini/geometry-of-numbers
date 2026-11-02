import SquaredStepBudget

namespace CarrySummableRadial
open Filter Topology
noncomputable section
set_option autoImplicit false

theorem squared_step_scaled (f : ℝ → ℝ) (a b B : ℝ) (hba : b≤a)
    (hf : ∀ x ∈ Set.Icc b a, DifferentiableAt ℝ f x)
    (hd : ∀ x ∈ Set.Icc b a, |deriv f x|≤2*B*x) :
    |f a-f b|≤B*(a^2-b^2) := by
  have hp (x : ℝ) (hx : x∈Set.Icc b a) :
      HasDerivAt (fun x => B*x^2+f x) (2*B*x+deriv f x) x := by
    convert ((hasDerivAt_pow 2 x).const_mul B).add (hf x hx).hasDerivAt using 1
    all_goals try rfl
    all_goals ring
  have hm (x : ℝ) (hx : x∈Set.Icc b a) :
      HasDerivAt (fun x => B*x^2-f x) (2*B*x-deriv f x) x := by
    convert ((hasDerivAt_pow 2 x).const_mul B).sub (hf x hx).hasDerivAt using 1
    all_goals try rfl
    all_goals ring
  have hpmono : MonotoneOn (fun x => B*x^2+f x) (Set.Icc b a) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc b a)
    · intro x hx
      exact (hp x hx).continuousAt.continuousWithinAt
    · intro x hx
      exact (hp x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [(hp x (interior_subset hx)).deriv]
      have hh := (abs_le.mp (hd x (interior_subset hx))).1
      linarith
  have hmmono : MonotoneOn (fun x => B*x^2-f x) (Set.Icc b a) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc b a)
    · intro x hx
      exact (hm x hx).continuousAt.continuousWithinAt
    · intro x hx
      exact (hm x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [(hm x (interior_subset hx)).deriv]
      have hh := (abs_le.mp (hd x (interior_subset hx))).2
      linarith
  have hpba := hpmono ⟨le_rfl,hba⟩ ⟨hba,le_rfl⟩ hba
  have hmba := hmmono ⟨le_rfl,hba⟩ ⟨hba,le_rfl⟩ hba
  exact abs_le.mpr ⟨by nlinarith,by nlinarith⟩

end
end CarrySummableRadial
