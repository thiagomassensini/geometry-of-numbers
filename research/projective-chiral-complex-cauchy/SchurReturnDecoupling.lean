import PhysicalRadialAllOrderDeterminant
import BinomialInverse

/-!
# The old-side Newton difference of a signed trace

The right input is a raw sample combination. Newton recovery from the
existing two-sided normalized kernel gives its old-side limit, including
all crossings, without assuming a sign on a full or reduced form.
-/

namespace CarrySchurDecoupling

open CarrySelfAdjointOperator CarryNativeBinomial Filter Topology
open scoped Matrix BigOperators
noncomputable section
set_option autoImplicit false

/-- Undo the divided-difference scale with the unsigned Newton chart. -/
def newtonRecovery (h : ℂ) (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.diagonal (fun r : Fin N => (r.val.factorial : ℂ) * h ^ r.val) *
    binomialMatrix N

theorem forwardTransform_mul_newtonRecovery (h : ℂ) (N : ℕ) (hh : h ≠ 0) :
    completedGreenComplexForwardDifferenceTransform h N * newtonRecovery h N = 1 := by
  unfold newtonRecovery
  rw [← Matrix.mul_assoc, ← signed_binomial_mul N]
  congr 1
  ext i r
  rw [Matrix.mul_diagonal]
  change
    (((r.val.factorial : ℂ) * h ^ r.val)⁻¹) *
        ((((-1 : ℤ) ^ (r.val - i.val) * r.val.choose i.val : ℤ) : ℂ)) *
          ((r.val.factorial : ℂ) * h ^ r.val) =
      completedGreenForwardWeight r.val i.val
  have hn : ((r.val.factorial : ℂ) * h ^ r.val) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero r.val) (pow_ne_zero _ hh)
  rw [mul_right_comm, inv_mul_cancel₀ hn, one_mul]
  rfl

/-- The Newton chart tends to the same zeroth column at every raw address. -/
theorem newtonRecovery_radial_tendsto (N : ℕ) :
    Tendsto (fun k => newtonRecovery (canonicalCompletedC3RadialSecondStep k) N) atTop
      (nhds (fun i _ : Fin N => if i.val = 0 then (1 : ℂ) else 0)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  simp only [newtonRecovery, Matrix.diagonal_mul, binomialMatrix]
  have hh := ((canonicalCompletedC3RadialSecondStep_tendsto_zero.pow i.val).const_mul
    (i.val.factorial : ℂ)).mul
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (j.val.choose i.val : ℂ))
        atTop (nhds (j.val.choose i.val : ℂ)))
  by_cases hi : i.val = 0
  · simpa only [Function.comp_def, hi, pow_zero, Nat.factorial_zero, Nat.cast_one,
      Nat.choose_zero_right, mul_one, if_pos] using hh
  · have hz : (0 : ℂ) ^ i.val = 0 := zero_pow hi
    rw [hz, mul_zero, zero_mul] at hh
    simpa only [Function.comp_def, if_neg hi] using hh

private theorem shiftedSample_eq_radialDslope (k N : ℕ) :
    completedGreenComplexShiftedKernelSampleMatrix canonicalCompletedNativePolarizedDslopeKernel
      (canonicalCompletedC3RadialSecondStep k) N =
      canonicalCompletedNativeRadialDslopeSampleMatrix k N := by
  ext i j
  simp only [canonicalCompletedNativeRadialDslopeSampleMatrix, Matrix.of_apply,
    completedGreenComplexShiftedKernelSampleMatrix,
    canonicalCompletedC3RadialTiltPoint_eq_step_add_nsmul]
  congr 1 <;> push_cast <;> simp [nsmul_eq_mul] <;> ring

/-- Remove the right stencil exactly. This equality holds on the original
grid, including the new source address, with no limiting operation. -/
theorem radial_single_side_eq_confluent_mul_newton (k N : ℕ) :
    (completedGreenComplexForwardDifferenceTransform
      (canonicalCompletedC3RadialSecondStep k) N)ᴴ *
      canonicalCompletedNativeRadialDslopeSampleMatrix k N =
    completedGreenComplexShiftedKernelForwardDifferenceMatrix
      canonicalCompletedNativePolarizedDslopeKernel
      (canonicalCompletedC3RadialSecondStep k) N *
      newtonRecovery (canonicalCompletedC3RadialSecondStep k) N := by
  unfold completedGreenComplexShiftedKernelForwardDifferenceMatrix
  rw [shiftedSample_eq_radialDslope, Matrix.mul_assoc _ _
    (newtonRecovery (canonicalCompletedC3RadialSecondStep k) N)]
  rw [forwardTransform_mul_newtonRecovery _ _
    (canonicalCompletedC3RadialSecondStep_ne_zero k), Matrix.mul_one]

/-- Every old difference against any raw sample has the same centered
coefficient in the right slot. The quantifier ranges over all orders in
every fixed finite grid. -/
theorem radial_single_side_tendsto (N : ℕ) (i j : Fin N) :
    Tendsto (fun k =>
      ((completedGreenComplexForwardDifferenceTransform
        (canonicalCompletedC3RadialSecondStep k) N)ᴴ *
          canonicalCompletedNativeRadialDslopeSampleMatrix k N) i j) atTop
      (nhds (polarizedGreenMomentCoefficient canonicalCompletedNativeLogDerivativeMoment i.val 0)) := by
  have hc := radialDslopeConfluent_tendsto N
  have hn := newtonRecovery_radial_tendsto N
  have ha (l : Fin N) := tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hc i) l
  have hb (l : Fin N) := tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hn l) j
  have h := tendsto_finsetSum Finset.univ (fun l (_ : l ∈ Finset.univ) => (ha l).mul (hb l))
  have hsum :
      (∑ l : Fin N, polarizedGreenMomentCoefficient
        canonicalCompletedNativeLogDerivativeMoment i.val l.val *
          (if l.val = 0 then (1 : ℂ) else 0)) =
        polarizedGreenMomentCoefficient canonicalCompletedNativeLogDerivativeMoment i.val 0 := by
    have hN : 0 < N := Nat.zero_lt_of_lt i.isLt
    letI : NeZero N := ⟨hN.ne'⟩
    simp only [← Fin.val_zero (n := N), Fin.val_inj, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [Matrix.of_apply] at h
  rw [hsum] at h
  apply h.congr'
  filter_upwards with k
  rw [radial_single_side_eq_confluent_mul_newton, Matrix.mul_apply]

/-- Applies to the actual positive-channel orthogonalization coefficients
once their raw limit is supplied. In the radial Cauchy projection this
limit is the fixed monic orthogonal-polynomial coefficient vector. -/
theorem radial_old_difference_raw_combination_tendsto (N : ℕ) (i : Fin N)
    (x : ℕ → Fin N → ℂ) (x₀ : Fin N → ℂ) (hx : Tendsto x atTop (nhds x₀)) :
    Tendsto (fun k =>
      (((completedGreenComplexForwardDifferenceTransform
        (canonicalCompletedC3RadialSecondStep k) N)ᴴ *
          canonicalCompletedNativeRadialDslopeSampleMatrix k N) *ᵥ x k) i) atTop
      (nhds (polarizedGreenMomentCoefficient canonicalCompletedNativeLogDerivativeMoment i.val 0 *
        ∑ j, x₀ j)) := by
  have h := tendsto_finsetSum Finset.univ (fun j (_ : j ∈ Finset.univ) =>
    (radial_single_side_tendsto N i j).mul (tendsto_pi_nhds.mp hx j))
  simpa only [Matrix.mulVec, dotProduct, Finset.mul_sum] using h

/-- Exact transport of the returned crossing after positive-channel
orthogonalization. The same identity holds for finite synthesis in the
TFVD trace carrier by substituting its two source maps. -/
theorem return_cross_eq_negative_signed_trace
    {p q m n : Type*} [Fintype p] [Fintype q] [Fintype m]
    (A₀ : Matrix p m ℂ) (B₀ : Matrix q m ℂ) (A₁ : Matrix p n ℂ) (B₁ : Matrix q n ℂ)
    (T : Matrix m m ℂ) (horth : A₀ᴴ * A₁ = 0) :
    Tᴴ * (B₀ᴴ * B₁) = -(Tᴴ * (A₀ᴴ * A₁ - B₀ᴴ * B₁)) := by
  rw [horth, zero_sub, Matrix.mul_neg, neg_neg]

#print axioms radial_old_difference_raw_combination_tendsto
#print axioms return_cross_eq_negative_signed_trace

end
end CarrySchurDecoupling
