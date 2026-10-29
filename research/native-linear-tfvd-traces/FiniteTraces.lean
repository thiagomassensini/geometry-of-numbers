import ResponseTaylor

namespace CarryLinearTfvd
open CarrySelfAdjointOperator NativeCauchyPorts CarryNativeTfvd CarryCriticalTfvd
open scoped BigOperators
noncomputable section
set_option autoImplicit false

/-- The old response weight p₁(j)=j+1, with the original zero-based bulk. -/
theorem linear_commutator_succ (eta : ℝ) (c : ℕ →₀ ℂ) (j : ℕ) :
    completionCommutator eta (monomialWeight 1) c (j+1) =
      (eta : ℂ)⁻¹*c (j+2)-(eta : ℂ)*c j := by
  rw [completion_commutator_succ]
  simp only [monomialWeight, pow_one, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  ring

/-- Both initial coefficients survive the literal unilateral shift. No inverse
of the physical multiplier and no sign assumption is involved. -/
theorem linear_commutator_shift_numerator (eta : ℝ) (c : ℕ →₀ ℂ) :
    coefficientShift (completionCommutator eta (monomialWeight 1) c) =
      (eta : ℂ)⁻¹ • (c-Finsupp.single 0 (c 0)-Finsupp.single 1 (c 1)) -
        (eta : ℂ) • coefficientShift (coefficientShift c) := by
  ext j
  rcases j with _ | _ | j
  all_goals simp [coefficientShift_zero, coefficientShift_succ,
    completion_commutator_zero, linear_commutator_succ, Nat.add_assoc]

/-- The same numerator obtained from the EXISTING TFVD two-trace theorem.
The extra center term is retained rather than hidden in a redefined bulk. -/
theorem linear_commutator_tfvd_numerator (eta : ℝ) (c : ℕ →₀ ℂ) :
    coefficientShift (completionCommutator eta (monomialWeight 1) c) =
      coefficientShift (finiteTfvdBulk eta c) + (2 : ℂ) • coefficientShift c -
        (2*(eta : ℂ)) • coefficientShift (coefficientShift c) -
        Finsupp.single 1 (2*c 0) := by
  rw [linear_commutator_shift_numerator]
  have ht := finiteCoefficientValve_two_traces eta c
  calc
    _ = finiteCoefficientValve eta c + (2 : ℂ) • coefficientShift c -
        (2*(eta : ℂ)) • coefficientShift (coefficientShift c) -
        (eta : ℂ)⁻¹ • Finsupp.single 0 (c 0) -
        (eta : ℂ)⁻¹ • Finsupp.single 1 (c 1) := by
      simp only [finiteCoefficientValve]
      module
    _ = _ := by
      rw [ht]
      ext j
      rcases j with _ | _ | j
      all_goals simp [finiteTrace0, finiteTrace1] <;> ring

end
end CarryLinearTfvd
