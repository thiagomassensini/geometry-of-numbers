import TailControls

namespace CarryEffectiveRadial
open CarrySelfAdjointOperator CarryBoundaryReconstruction
open Filter Topology
noncomputable section
set_option autoImplicit false

/-- A variable derivative budget integrates exactly against h², rather
than a constant Lipschitz budget which would lose the radial scale. -/
theorem squared_step_budget (f : ℝ → ℝ) (a b : ℝ) (hba : b≤a)
    (hf : ∀ x ∈ Set.Icc b a, DifferentiableAt ℝ f x)
    (hd : ∀ x ∈ Set.Icc b a, |deriv f x|≤2*x) :
    |f a-f b|≤a^2-b^2 := by
  have hp (x : ℝ) (hx : x∈Set.Icc b a) :
      HasDerivAt (fun x => x^2+f x) (2*x+deriv f x) x := by
    convert (hasDerivAt_pow 2 x).add (hf x hx).hasDerivAt using 1
    all_goals first | rfl | norm_num
  have hm (x : ℝ) (hx : x∈Set.Icc b a) :
      HasDerivAt (fun x => x^2-f x) (2*x-deriv f x) x := by
    convert (hasDerivAt_pow 2 x).sub (hf x hx).hasDerivAt using 1
    all_goals first | rfl | norm_num
  have hpmono : MonotoneOn (fun x => x^2+f x) (Set.Icc b a) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc b a)
    · intro x hx
      exact (hp x hx).continuousAt.continuousWithinAt
    · intro x hx
      exact (hp x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [(hp x (interior_subset hx)).deriv]
      have hh := (abs_le.mp (hd x (interior_subset hx))).1
      linarith
  have hmmono : MonotoneOn (fun x => x^2-f x) (Set.Icc b a) := by
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
  exact abs_le.mpr ⟨by linarith,by linarith⟩

/-- A proved increment budget gives absolute summability at the SAME
explicit anchor, without relying on an unknown monotonicity cutoff. -/
theorem radial_budget_hasSum (f : ℕ → ℝ) (L B : ℝ)
    (hf : Tendsto f atTop (nhds L)) (K : ℕ)
    (hb : ∀ j, |f (K+j)-f (K+j+1)|≤B*
      ((radialFourSourceStep (K+j))^2-(radialFourSourceStep (K+j+1))^2)) :
    HasSum (fun j => f (K+j)-f (K+j+1)) (f K-L) ∧
    Summable (fun j => |f (K+j)-f (K+j+1)|) ∧
    (∑' j, |f (K+j)-f (K+j+1)|)≤B*(radialFourSourceStep K)^2 := by
  have hg : HasSum (fun j => (radialFourSourceStep (K+j))^2-
      (radialFourSourceStep (K+j+1))^2) ((radialFourSourceStep K)^2) := by
    have hn (j : ℕ) : 0≤(radialFourSourceStep (K+j))^2-(radialFourSourceStep (K+j+1))^2 := by
      have hp := radial_step_positive (K+j)
      have hq := radial_step_positive (K+j+1)
      have hd := radial_step_decreasing (K+j)
      nlinarith
    simpa only [sub_zero] using radial_drop_hasSum (fun k => (radialFourSourceStep k)^2) 0
      (by simpa using radial_step_tendsto.pow 2) K hn
  have hBg := hg.mul_left B
  have ha := Summable.of_nonneg_of_le (fun j => abs_nonneg (f (K+j)-f (K+j+1))) hb hBg.summable
  have hs : Summable (fun j => f (K+j)-f (K+j+1)) :=
    ha.of_norm_bounded (fun j => by rw [Real.norm_eq_abs])
  refine ⟨(hs.hasSum_iff_tendsto_nat).mpr (radial_partial_sum_tendsto f L hf K),ha,?_⟩
  have hh := ha.tsum_le_tsum hb hBg.summable
  rwa [hBg.tsum_eq] at hh

end
end CarryEffectiveRadial
