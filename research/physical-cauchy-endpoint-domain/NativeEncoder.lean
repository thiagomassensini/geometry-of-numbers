import EndpointGreen
import CriticalReadout

namespace CarryPhysicalTrace
open CarrySelfAdjointOperator CarrySelfAdjointOperator.NativeLaguerre
open CarrySelfAdjointOperator.PhysicalSewing Polynomial
open scoped BigOperators
noncomputable section
set_option autoImplicit false

/-- Literal polynomial calculus, not a fitted generator of canonical moments. -/
theorem euler_polynomial (c : ℕ →₀ ℂ) :
    Polynomial.ofFinsupp (AddMonoidAlgebra.ofCoeff (coefficientEuler c)) =
      Polynomial.ofFinsupp (AddMonoidAlgebra.ofCoeff c) + X * (Polynomial.ofFinsupp (AddMonoidAlgebra.ofCoeff c)).derivative := by
  ext j
  cases j with
  | zero => simp [coefficient_euler_apply]
  | succ j =>
      rw [Polynomial.coeff_add,Polynomial.coeff_X_mul,Polynomial.coeff_derivative]
      change coefficientEuler c (j+1) = c (j+1) + c (j+1)*(j+1)
      rw [coefficient_euler_apply]
      push_cast
      ring

/-- The existing material polynomial is embedded in its original Cauchy span. -/
def finiteMaterialState (N : ℕ) (v : Fin N → ℂ) : EndpointDomain :=
  coefficientEquiv (materialPolynomial N v).toFinsupp.coeff

theorem finite_material_state_coe (N : ℕ) (v : Fin N → ℂ) :
    (finiteMaterialState N v : PhysicalCauchySpace) = physicalFiniteSynthesis N v := by
  have hN : (materialPolynomial N v).toFinsupp.coeff.support ⊆ Finset.range N := by
    intro j hj
    by_contra h
    have hle : N ≤ j := by simpa using h
    have he : (materialPolynomial N v).coeff j = 0 := ofFn_coeff_eq_zero_of_ge v hle
    exact (Finsupp.mem_support_iff.mp hj) he
  rw [finiteMaterialState,coefficient_equiv_coe,embedding_eq_finite _ N hN]
  congr 1
  funext j
  exact ofFn_coeff_eq_val_of_lt v j.isLt

theorem endpoint_trace_finite_material (N : ℕ) (v : Fin N → ℂ) (a : ℕ) :
    endpointTrace a (finiteMaterialState N v) =
      ∑ j : Fin N, (j.val.descFactorial a : ℂ)*v j := by
  rw [finiteMaterialState,endpoint_trace_coefficients]
  have hN : (materialPolynomial N v).toFinsupp.coeff.support ⊆ Finset.range N := by
    intro j hj
    by_contra h
    have hle : N ≤ j := by simpa using h
    exact (Finsupp.mem_support_iff.mp hj) (ofFn_coeff_eq_zero_of_ge v hle)
  rw [Finsupp.sum_of_support_subset _ hN _ (by simp),← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  rw [show (materialPolynomial N v).toFinsupp.coeff j.val = v j from ofFn_coeff_eq_val_of_lt v j.isLt]

/-- Exact original jet encoder, with its phase and radial step unaltered. -/
theorem native_encoder_trace (N k : ℕ) (v : Fin N → ℂ) (a : Fin N) :
    physicalEndpointJetInput N k v a =
      endpointGauge k a * endpointTrace a (finiteMaterialState N v) := by
  rw [physicalEndpointJetInput_finite,endpoint_trace_finite_material]

end
end CarryPhysicalTrace
