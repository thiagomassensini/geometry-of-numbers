import NativeTangent
import CarrySelfAdjointOperator.CompletedC3FullWronskianCentralChiralEnergy

/-! Scale of the Schur negative-channel metric on the original anchor. -/
namespace CarryCauchyResidual

open CarrySelfAdjointOperator CarryPositiveSquare
open Filter Topology
noncomputable section
set_option autoImplicit false

/-- On the old returned direction, the metric I + B P^-1 B* has this
eigenvalue. The positive and negative anchor vectors are proportional with
the original multiplier oneReturn. -/
def anchorNegativeGain (k : ℕ) : ℝ :=
  1 + Complex.normSq (oneReturn k) / oneDeficit k

theorem anchorNegativeGain_eq_inv (k : ℕ) (hd : oneDeficit k ≠ 0) :
    anchorNegativeGain k = (oneDeficit k)⁻¹ := by
  unfold anchorNegativeGain
  have h : oneDeficit k + Complex.normSq (oneReturn k) = 1 := by
    unfold oneDeficit
    ring
  field_simp [hd]
  linarith

/-- No later pivot is used. The old returned direction costs asymptotically
1/(8 h0 t), with t the mesh size of the original Cauchy carrier. -/
theorem anchorNegativeGain_rescaled_tendsto :
    Tendsto (fun k => anchorNegativeGain k / ((k : ℝ) + 1)) atTop
      (nhds (1 / (8 * canonicalCompletedNativeLogDerivativeMoment 0))) := by
  have hL : 0 < 8 * canonicalCompletedNativeLogDerivativeMoment 0 :=
    mul_pos (by norm_num) canonicalCompletedNativeLogDerivativeMoment_zero_pos
  have hinv := (tendsto_const_nhds :
    Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)).div central_deficit_tangent hL.ne'
  refine hinv.congr' ?_
  filter_upwards [central_deficit_tangent.eventually (eventually_ne_nhds hL.ne')]
    with k hk
  have hd : oneDeficit k ≠ 0 := fun h => hk (by simp [h])
  change 1 / (oneDeficit k * ((k : ℝ) + 1)) = _
  rw [anchorNegativeGain_eq_inv k hd, div_eq_mul_inv, mul_inv_rev, one_mul, mul_comm]
  rfl

#print axioms anchorNegativeGain_rescaled_tendsto

end
end CarryCauchyResidual
