import ResidualReturn

namespace CarryCauchyResidual
open CarrySelfAdjointOperator ChiralReturn CarryReturnDeflation CarryPositiveSquare
open scoped InnerProductSpace ComplexConjugate BigOperators
noncomputable section
set_option autoImplicit false

/-- Synthetic diagonal return on the ORIGINAL Cauchy tail carrier. These
two numbers are a logical control, not the native completed quotient. -/
def controlMultiplier : Fin 2 → ℂ := ![1/2,-1/2]
def controlCoefficients : Fin 2 → ℂ := ![1,-1]
def controlPair (c d : Fin 2 → ℂ) : ℂ :=
  inner ℂ (tailSynthesis 0 2 c) (tailSynthesis 0 2 d) -
    inner ℂ (tailSynthesis 0 2 (fun i => c i*controlMultiplier i))
      (tailSynthesis 0 2 (fun i => d i*controlMultiplier i))

theorem control_diagonal_contracts (i : Fin 2) : ‖controlMultiplier i‖^2 = 1/4 := by
  fin_cases i <;> norm_num [controlMultiplier, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]

private theorem tail_inner (c d : Fin 2 → ℂ) :
    inner ℂ (tailSynthesis 0 2 c) (tailSynthesis 0 2 d) =
      conj (c 0)*d 0/4+conj (c 0)*d 1/5+conj (c 1)*d 0/5+conj (c 1)*d 1/6 := by
  simp only [tailSynthesis, LinearMap.coe_mk, AddHom.coe_mk, Fin.sum_univ_two,
    inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, feature_inner]
  norm_num [cauchy]
  ring

theorem control_first_diagonal : controlPair (Pi.single 0 1) (Pi.single 0 1) = 3/16 := by
  rw [controlPair, tail_inner, tail_inner]
  norm_num [controlMultiplier, Pi.single_apply, map_div₀, map_ofNat]

theorem control_second_diagonal : controlPair (Pi.single 1 1) (Pi.single 1 1) = 1/8 := by
  rw [controlPair, tail_inner, tail_inner]
  norm_num [controlMultiplier, Pi.single_apply, map_div₀, map_ofNat]

theorem control_cross : controlPair (Pi.single 0 1) (Pi.single 1 1) = 1/4 := by
  rw [controlPair, tail_inner, tail_inner]
  norm_num [controlMultiplier, Pi.single_apply, map_div₀, map_ofNat]

/-- Positive diagonal deficits do NOT control the full Cauchy multiplier.
The exact obstruction is the cross term of the same physical norm. -/
theorem control_full_negative : controlPair controlCoefficients controlCoefficients = -3/16 := by
  rw [controlPair, tail_inner, tail_inner]
  norm_num [controlMultiplier, controlCoefficients, map_div₀, map_ofNat]

end
end CarryCauchyResidual
