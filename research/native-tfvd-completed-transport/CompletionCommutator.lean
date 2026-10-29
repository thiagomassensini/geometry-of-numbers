import ShiftTransport

namespace CarryNativeTfvd
open CarrySelfAdjointOperator NativeCauchyPorts
open scoped BigOperators
noncomputable section
set_option autoImplicit false

/-- Literal multiplication of finite coefficients by an address-dependent
source weight. Its support is contained in the original coefficient support. -/
def coefficientWeight (w : ℕ → ℂ) (c : ℕ →₀ ℂ) : ℕ →₀ ℂ :=
  Finsupp.onFinset c.support (fun j => w j * c j) (by
    intro j hj
    exact Finsupp.mem_support_iff.mpr (mul_ne_zero_iff.mp hj).2)

theorem coefficient_weight_apply (w : ℕ → ℂ) (c : ℕ →₀ ℂ) (j : ℕ) :
    coefficientWeight w c j = w j * c j := rfl

/-- The exact commutator; it is not discarded or absorbed into a new source. -/
def completionCommutator (eta : ℝ) (w : ℕ → ℂ) (c : ℕ →₀ ℂ) : ℕ →₀ ℂ :=
  finiteTfvdBulk eta (coefficientWeight w c) - coefficientWeight w (finiteTfvdBulk eta c)

theorem completion_commutator_zero (eta : ℝ) (w : ℕ → ℂ) (c : ℕ →₀ ℂ) :
    completionCommutator eta w c 0 = 0 := by
  simp [completionCommutator, coefficient_weight_apply, finiteTfvdBulk_zero]

theorem completion_commutator_succ (eta : ℝ) (w : ℕ → ℂ) (c : ℕ →₀ ℂ) (j : ℕ) :
    completionCommutator eta w c (j + 1) =
      (eta : ℂ)⁻¹ * (w (j + 2) - w (j + 1)) * c (j + 2) +
      (eta : ℂ) * (w j - w (j + 1)) * c j := by
  simp only [completionCommutator, Finsupp.sub_apply, finiteTfvdBulk_succ,
    coefficient_weight_apply]
  ring

theorem completion_bulk_split (eta : ℝ) (w : ℕ → ℂ) (c : ℕ →₀ ℂ) :
    finiteTfvdBulk eta (coefficientWeight w c) =
      coefficientWeight w (finiteTfvdBulk eta c) + completionCommutator eta w c := by
  unfold completionCommutator
  abel

theorem completion_commutator_constant (eta : ℝ) (a : ℂ) (c : ℕ →₀ ℂ) :
    completionCommutator eta (fun _ => a) c = 0 := by
  ext j
  cases j with
  | zero => simp [completion_commutator_zero]
  | succ j => simp [completion_commutator_succ]

/-- Completion and quotient contributions remain separately identifiable. -/
theorem completion_commutator_product (eta : ℝ) (a b : ℕ → ℂ) (c : ℕ →₀ ℂ) :
    completionCommutator eta (fun j => a j * b j) c =
      completionCommutator eta a (coefficientWeight b c) +
        coefficientWeight a (completionCommutator eta b c) := by
  ext j
  cases j with
  | zero => simp [completion_commutator_zero, coefficient_weight_apply]
  | succ j =>
    simp only [Finsupp.add_apply, completion_commutator_succ, coefficient_weight_apply]
    ring

/-- Commutation with the complete centered TFVD bracket is rigid: a diagonal
source weight must be constant if the commutator vanishes on every finite input. -/
theorem completion_commutator_vanishes_iff (eta : ℝ) (heta : eta ≠ 0) (w : ℕ → ℂ) :
    (∀ c : ℕ →₀ ℂ, completionCommutator eta w c = 0) ↔
      ∀ j : ℕ, w j = w 0 := by
  have he : (eta : ℂ) ≠ 0 := by exact_mod_cast heta
  constructor
  · intro h
    have hfirst := DFunLike.congr_fun (h (Finsupp.single 0 1)) 1
    rw [completion_commutator_succ eta w (Finsupp.single 0 1) 0] at hfirst
    have h10 : w 1 = w 0 := by
      simp only [Finsupp.single_eq_same, Finsupp.single_eq_of_ne (by omega : 2 ≠ 0),
        mul_zero, mul_one, zero_add, Finsupp.zero_apply] at hfirst
      exact (sub_eq_zero.mp ((mul_eq_zero.mp hfirst).resolve_left he)).symm
    have hnext (j : ℕ) : w (j + 2) = w (j + 1) := by
      have hj := DFunLike.congr_fun (h (Finsupp.single (j + 2) 1)) (j + 1)
      rw [completion_commutator_succ] at hj
      simp only [Finsupp.single_eq_same,
        Finsupp.single_eq_of_ne (by omega : j ≠ j + 2),
        mul_zero, mul_one, add_zero, Finsupp.zero_apply] at hj
      exact sub_eq_zero.mp ((mul_eq_zero.mp hj).resolve_left (inv_ne_zero he))
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      cases j with
      | zero => exact h10
      | succ j => exact (hnext j).trans ih
  · intro h c
    have hw : w = fun _ => w 0 := funext h
    rw [hw]
    exact completion_commutator_constant eta (w 0) c

end
end CarryNativeTfvd
