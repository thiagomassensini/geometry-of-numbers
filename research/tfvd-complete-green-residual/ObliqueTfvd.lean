import CompleteTfvd

/-! The exact causal TFVD splitting is complementary but oblique in the
ORIGINAL vertical Hilbert metric. A finite-support witness works at the
native critical ratio. No new source or replacement metric is introduced. -/
namespace CarryCompleteTfvd
open GeometryOfNumbers.Analysis GeometryOfNumbers.Analysis.RealCarry
open scoped BigOperators InnerProductSpace lp ENNReal
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000

def verticalGreen (eta : ℝ) : CarryVerticalL2 →L[ℝ] CarryVerticalL2 :=
  (carryVerticalL2WeightedGreen eta).comp (carryWeightedVerticalCenteredBracket eta)

def verticalReturn (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    CarryVerticalL2 →L[ℝ] CarryVerticalL2 :=
  (carryWeightedVerticalReturn eta h0.le h1).comp (carryWeightedVerticalTrace eta)

theorem vertical_reconstruct (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (x : CarryVerticalL2) : verticalGreen eta x + verticalReturn eta h0 h1 x = x := by
  exact DFunLike.congr_fun (carryWeightedVerticalTfvd_identity eta h0 h1) x

theorem vertical_return_idempotent (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (x : CarryVerticalL2) :
    verticalReturn eta h0 h1 (verticalReturn eta h0 h1 x) = verticalReturn eta h0 h1 x := by
  have ht := DFunLike.congr_fun (carryWeightedVerticalTrace_comp_return eta h0 h1)
    (carryWeightedVerticalTrace eta x)
  change carryWeightedVerticalTrace eta
    (carryWeightedVerticalReturn eta h0.le h1 (carryWeightedVerticalTrace eta x)) =
    carryWeightedVerticalTrace eta x at ht
  exact congrArg (carryWeightedVerticalReturn eta h0.le h1) ht

theorem vertical_green_return_zero (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (x : CarryVerticalL2) : verticalGreen eta (verticalReturn eta h0 h1 x) = 0 := by
  have h := vertical_reconstruct eta h0 h1 (verticalReturn eta h0 h1 x)
  rw [vertical_return_idempotent] at h
  exact add_right_cancel (by simpa using h :
    verticalGreen eta (verticalReturn eta h0 h1 x) + verticalReturn eta h0 h1 x =
    0 + verticalReturn eta h0 h1 x)

theorem vertical_return_green_zero (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (x : CarryVerticalL2) : verticalReturn eta h0 h1 (verticalGreen eta x) = 0 := by
  have h := congrArg (verticalReturn eta h0 h1) (vertical_reconstruct eta h0 h1 x)
  rw [map_add, vertical_return_idempotent] at h
  exact add_right_cancel (by simpa using h :
    verticalReturn eta h0 h1 (verticalGreen eta x) + verticalReturn eta h0 h1 x =
    0 + verticalReturn eta h0 h1 x)

theorem vertical_green_idempotent (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (x : CarryVerticalL2) : verticalGreen eta (verticalGreen eta x) = verticalGreen eta x := by
  have h := vertical_reconstruct eta h0 h1 (verticalGreen eta x)
  simpa only [vertical_return_green_zero, add_zero] using h

/-- Both ordered crossings in the ORIGINAL metric, with independent inputs. -/
theorem vertical_pairing (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (x y : CarryVerticalL2) :
    inner ℝ x y = inner ℝ (verticalGreen eta x) (verticalGreen eta y) +
      inner ℝ (verticalGreen eta x) (verticalReturn eta h0 h1 y) +
      inner ℝ (verticalReturn eta h0 h1 x) (verticalGreen eta y) +
      inner ℝ (verticalReturn eta h0 h1 x) (verticalReturn eta h0 h1 y) := by
  calc
    _ = inner ℝ (verticalGreen eta x+verticalReturn eta h0 h1 x)
      (verticalGreen eta y+verticalReturn eta h0 h1 y) := by rw [vertical_reconstruct, vertical_reconstruct]
    _ = _ := by simp only [inner_add_left, inner_add_right]; ring

theorem vertical_energy (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (x : CarryVerticalL2) :
    ‖x‖^2 = ‖verticalGreen eta x‖^2+‖verticalReturn eta h0 h1 x‖^2 +
      2*inner ℝ (verticalGreen eta x) (verticalReturn eta h0 h1 x) := by
  calc
    _ = ‖verticalGreen eta x+verticalReturn eta h0 h1 x‖^2 := by rw [vertical_reconstruct]
    _ = _ := by rw [norm_add_sq_real]; ring

theorem vertical_green_single_two (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    verticalGreen eta (lp.single 2 2 (1:ℝ)) = lp.single 2 2 (1:ℝ) := by
  have ht : carryWeightedVerticalTrace eta (lp.single 2 2 (1:ℝ)) = 0 := by
    simp [carryWeightedVerticalTrace_apply, lp.single_apply]
  have hr : verticalReturn eta h0 h1 (lp.single 2 2 (1:ℝ)) = 0 := by
    change carryWeightedVerticalReturn eta h0.le h1
      (carryWeightedVerticalTrace eta (lp.single 2 2 (1:ℝ))) = 0
    rw [ht, map_zero]
  simpa only [hr, add_zero] using vertical_reconstruct eta h0 h1 (lp.single 2 2 (1:ℝ))

/-- Exact, negative mixed pairing of two actual causal TFVD channels. -/
theorem vertical_mixed_witness (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    inner ℝ (verticalGreen eta (lp.single 2 2 (1:ℝ)))
      (verticalReturn eta h0 h1 (lp.single 2 0 (1:ℝ))) = -eta^2 := by
  rw [vertical_green_single_two eta h0 h1, lp.inner_single_left]
  simp only [RCLike.inner_apply, map_one, mul_one]
  change carryWeightedVerticalReturn eta h0.le h1
    (carryWeightedVerticalTrace eta (lp.single 2 0 (1:ℝ))) 2 = _
  rw [carryWeightedVerticalReturn_apply, carryWeightedVerticalTrace_apply]
  norm_num [lp.single_apply]

theorem vertical_not_orthogonal (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    ¬ ∀ x y : CarryVerticalL2, inner ℝ (verticalGreen eta x) (verticalReturn eta h0 h1 y) = 0 := by
  intro h
  have he := h (lp.single 2 2 (1:ℝ)) (lp.single 2 0 (1:ℝ))
  rw [vertical_mixed_witness] at he
  have hp : 0 < eta^2 := sq_pos_of_pos h0
  linarith

/-- Native eta_2 has eta_2²=1/2, so the mixed pairing is exactly -1/2. -/
theorem critical_two_mixed_witness :
    inner ℝ (verticalGreen (criticalVerticalAmplitudeRatio 2 (by norm_num)) (lp.single 2 2 (1:ℝ)))
      (verticalReturn (criticalVerticalAmplitudeRatio 2 (by norm_num))
        (criticalVerticalAmplitudeRatio_pos 2 _) (criticalVerticalAmplitudeRatio_lt_one 2 (by norm_num))
        (lp.single 2 0 (1:ℝ))) = -(1/2:ℝ) := by
  rw [vertical_mixed_witness, criticalVerticalAmplitudeRatio_eq_rpow]
  change -((2:ℝ)^(-(1:ℝ)/2))^(2:ℕ) = _
  rw [← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

end
end CarryCompleteTfvd
