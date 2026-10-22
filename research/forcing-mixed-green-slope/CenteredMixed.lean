import MixedLedger

namespace CarryMixedGreen
open GeometryOfNumbers.Analysis GeometryOfNumbers.Analysis.BaseTwoCompletion
open CarryForcingResidual CarryCompletedGreenBalance
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000

def companionCoefficient (t u : ℝ) : ℂ :=
  -(carryMaterialResponseScale:ℂ)*
    (conj (carryMaterialClockForcingScalar t)*companionProbe u +
      conj (companionProbe t)*carryMaterialClockForcingScalar u)

/-- Literal off-diagonal quotient. Its value at u=t uses total field
division, and is NOT asserted to be a confluent physical extension. -/
def retainedCoefficient (t u : ℝ) : ℂ :=
  ((carryMaterialResponseScale^2*t*u:ℝ):ℂ)*
    ((conj (valueProbe t)*carryMaterialClockForcingScalar u -
      conj (carryMaterialClockForcingScalar t)*valueProbe u)/((u-t:ℝ):ℂ))

theorem mixed_regular_split (t u : ℝ) (hne : u ≠ t) :
    mixedForcingGreen t u / ((u-t:ℝ):ℂ) =
      companionCoefficient t u + retainedCoefficient t u := by
  have he := mixed_hidden_regular t u hne
  unfold mixedHiddenGreen at he
  rw [sub_div] at he
  unfold companionCoefficient retainedCoefficient
  linear_combination he

theorem scalar_forcing_centered {N : ℕ} (c : Fin N → ℂ) (t : Fin N → ℝ) :
    ∑ i, centeredCoefficients c t i * carryMaterialClockForcingScalar (centeredParameters t i) = 0 := by
  simp only [centeredCoefficients, centeredParameters, Fin.sum_univ_succ,
    Fin.cons_zero, Fin.cons_succ]
  rw [div_mul_cancel₀ _ forcing_scalar_zero_ne, neg_add_cancel]

theorem companion_bilinear {N M : ℕ} (c : Fin N → ℂ) (d : Fin M → ℂ)
    (t : Fin N → ℝ) (u : Fin M → ℝ) :
    (∑ i, ∑ j, conj (c i)*companionCoefficient (t i) (u j)*d j) =
      -(carryMaterialResponseScale:ℂ)*
        (conj (∑ i, c i*carryMaterialClockForcingScalar (t i))*(∑ j, d j*companionProbe (u j)) +
          conj (∑ i, c i*companionProbe (t i))*(∑ j, d j*carryMaterialClockForcingScalar (u j))) := by
  have sep (f : Fin N → ℂ) (g : Fin M → ℂ) :
      (∑ i, ∑ j, conj (c i)*conj (f i)*g j*d j) =
        conj (∑ i, c i*f i)*(∑ j, d j*g j) := by
    simp only [map_sum, map_mul]
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have he : (∑ i, ∑ j, conj (c i)*companionCoefficient (t i) (u j)*d j) =
      -(carryMaterialResponseScale:ℂ)*
        ((∑ i, ∑ j, conj (c i)*conj (carryMaterialClockForcingScalar (t i))*companionProbe (u j)*d j) +
          (∑ i, ∑ j, conj (c i)*conj (companionProbe (t i))*carryMaterialClockForcingScalar (u j)*d j)) := by
    rw [mul_add]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    unfold companionCoefficient
    ring
  rw [he, sep, sep]

/-- NEW cancellation: the same source centering removes BOTH first-leg
crosses, not merely the forcing/forcing rank-one Gram. -/
theorem companion_centered_bilinear {N M : ℕ} (c : Fin N → ℂ) (d : Fin M → ℂ)
    (t : Fin N → ℝ) (u : Fin M → ℝ) :
    (∑ i, ∑ j, conj (centeredCoefficients c t i)*
      companionCoefficient (centeredParameters t i) (centeredParameters u j)*centeredCoefficients d u j) = 0 := by
  rw [companion_bilinear, scalar_forcing_centered, scalar_forcing_centered]
  simp

theorem retained_centered_bilinear {N M : ℕ} (c : Fin N → ℂ) (d : Fin M → ℂ)
    (t : Fin N → ℝ) (u : Fin M → ℝ) :
    (∑ i, ∑ j, conj (centeredCoefficients c t i)*
      retainedCoefficient (centeredParameters t i) (centeredParameters u j)*centeredCoefficients d u j) =
    ∑ i, ∑ j, conj (c i)*retainedCoefficient (t i) (u j)*d j := by
  rw [Fin.sum_univ_succ]
  simp only [centeredCoefficients, centeredParameters, Fin.cons_zero, Fin.cons_succ,
    retainedCoefficient, mul_zero, zero_mul, Complex.ofReal_zero,
    Finset.sum_const_zero, zero_add]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fin.sum_univ_succ]
  simp

/-- This is a statement about the explicit coefficient expression. Only
mixed_regular_split identifies it with a physical quotient, OFF diagonal. -/
theorem centered_mixed_coefficient {N M : ℕ} (c : Fin N → ℂ) (d : Fin M → ℂ)
    (t : Fin N → ℝ) (u : Fin M → ℝ) :
    (∑ i, ∑ j, conj (centeredCoefficients c t i)*
      (companionCoefficient (centeredParameters t i) (centeredParameters u j) +
        retainedCoefficient (centeredParameters t i) (centeredParameters u j))*centeredCoefficients d u j) =
    ∑ i, ∑ j, conj (c i)*retainedCoefficient (t i) (u j)*d j := by
  simp only [mul_add, add_mul, Finset.sum_add_distrib]
  rw [companion_centered_bilinear, retained_centered_bilinear, zero_add]

theorem retained_regular_ratio (t u : ℝ)
    (ht : carryMaterialClockForcingScalar t ≠ 0)
    (hu : carryMaterialClockForcingScalar u ≠ 0) :
    retainedCoefficient t u =
      ((carryMaterialResponseScale^2*t*u:ℝ):ℂ)*
        conj (carryMaterialClockForcingScalar t)*carryMaterialClockForcingScalar u*
          ((valueRatio u - conj (valueRatio t))/((u-t:ℝ):ℂ)) := by
  rw [retainedCoefficient, retained_cross_ratio t u ht hu]
  ring

/-- Physical off-diagonal statement, without assigning a confluent value
to an isolated channel. The center terms use the original source pairs. -/
theorem mixed_regular_anchor (t u : ℝ) (ht : t ≠ 0) (hu : u ≠ 0) (hne : u ≠ t) :
    mixedForcingGreen t u / ((u-t:ℝ):ℂ) -
      conj (carryMaterialClockForcingScalar t/carryMaterialClockForcingScalar 0)*
        (mixedForcingGreen 0 u/(u:ℂ)) -
      (mixedForcingGreen t 0/((-t:ℝ):ℂ))*
        (carryMaterialClockForcingScalar u/carryMaterialClockForcingScalar 0) =
    retainedCoefficient t u := by
  have hz : companionProbe 0 = 0 := by
    simp [companionProbe, carryMaterialClock_compressed_pair_origin]
  have hl := mixed_regular_split 0 u hu
  have hr := mixed_regular_split t 0 (Ne.symm ht)
  simp only [sub_zero] at hl
  simp only [zero_sub] at hr
  rw [mixed_regular_split t u hne, hl, hr]
  simp only [retainedCoefficient, mul_zero, zero_mul, Complex.ofReal_zero,
    companionCoefficient, hz, map_zero, mul_zero, zero_mul, add_zero, zero_add, map_div₀]
  have hc : conj (carryMaterialClockForcingScalar 0) ≠ 0 := by simpa using forcing_scalar_zero_ne
  field_simp [forcing_scalar_zero_ne]
  ring

end
end CarryMixedGreen
