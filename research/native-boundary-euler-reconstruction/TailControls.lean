import SixBoundaryReconstruction

namespace CarryBoundaryReconstruction
open CarrySelfAdjointOperator Filter Topology
open scoped BigOperators
noncomputable section
set_option autoImplicit false

/-- A budget on ACTUAL increments bounds the entire accumulated radial tail.
This lemma does not discharge the source-specific budget premise. -/
theorem boundary_error_of_increment_budget (f : ℕ → ℝ) (L B : ℝ)
    (hf : Tendsto f atTop (nhds L)) (hB : 0≤B) (K : ℕ)
    (hb : ∀ j, |f (K+j)-f (K+j+1)|≤B*
      ((radialFourSourceStep (K+j))^2-(radialFourSourceStep (K+j+1))^2)) :
    |f K-L|≤B*(radialFourSourceStep K)^2 := by
  have hp (M : ℕ) : |∑ j ∈ Finset.range M, (f (K+j)-f (K+j+1))|≤
      B*(radialFourSourceStep K)^2 := by
    calc
      _ ≤ ∑ j ∈ Finset.range M, |f (K+j)-f (K+j+1)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.range M, B*((radialFourSourceStep (K+j))^2-
          (radialFourSourceStep (K+j+1))^2) := Finset.sum_le_sum (fun j _ => hb j)
      _ = B*((radialFourSourceStep K)^2-(radialFourSourceStep (K+M))^2) := by
        rw [← Finset.mul_sum]
        exact congrArg (fun z : ℝ => B*z)
          (radial_partial_sum (fun k => (radialFourSourceStep k)^2) K M)
      _ ≤ B*(radialFourSourceStep K)^2 := by
        nlinarith [mul_nonneg hB (sq_nonneg (radialFourSourceStep (K+M)))]
  exact le_of_tendsto ((continuous_abs.tendsto _).comp
    (radial_partial_sum_tendsto f L hf K)) (Filter.Eventually.of_forall hp)

theorem positive_boundary_of_increment_budget (f : ℕ → ℝ) (L B : ℝ)
    (hf : Tendsto f atTop (nhds L)) (hB : 0≤B) (K : ℕ)
    (hb : ∀ j, |f (K+j)-f (K+j+1)|≤B*
      ((radialFourSourceStep (K+j))^2-(radialFourSourceStep (K+j+1))^2))
    (ha : B*(radialFourSourceStep K)^2<f K) : 0<L := by
  have he := boundary_error_of_increment_budget f L B hf hB K hb
  have hd := le_trans (le_abs_self (f K-L)) he
  linarith

/-- Algebra control only: increments cannot detect an additive constant.
No modification of the native source is proposed. -/
theorem increments_ignore_constant (f : ℕ → ℝ) (c : ℝ) (k : ℕ) :
    (f k+c)-(f (k+1)+c)=f k-f (k+1) := by ring

/-- Exact obstruction to deducing a STRICT boundary sign from strict
positivity and strict decrease at every finite radial step. Abstract control
sequence only; it is not asserted to be another physical Carry source. -/
theorem positive_decreasing_zero_boundary : ∃ f : ℕ → ℝ,
    (∀ k, 0<f k) ∧ (∀ k, f (k+1)<f k) ∧ Tendsto f atTop (nhds 0) := by
  refine ⟨fun k => (radialFourSourceStep k)^2,?_,?_,?_⟩
  · intro k
    exact sq_pos_of_pos (radial_step_positive k)
  · intro k
    have hp := radial_step_positive k
    have hq := radial_step_positive (k+1)
    have hd := radial_step_decreasing k
    nlinarith
  · simpa using radial_step_tendsto.pow 2

end
end CarryBoundaryReconstruction
