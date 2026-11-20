import C3ImpulseLinearity
import C3TwentyThreeBoxes

/-!
Close the finite impulse-expansion obligation hCoeff, on the ORIGINAL
signed, common source trace. It is a linear map in the tail (unlike TT).
No independent parity source is substituted.
-/
namespace CarrySourceBezout
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1400000

theorem signedSourceLinear_add_tail
    (alpha betaA : ℝ) (bB bP : Bool) (rB rP : ℕ)
    (zB : Fin rB → ℝ) (zP : Fin rP → ℝ)
    (H T U : ℕ → ℂ) :
    signedSourceLinear alpha betaA bB bP rB rP zB zP H (T+U) =
      signedSourceLinear alpha betaA bB bP rB rP zB zP H T +
      signedSourceLinear alpha betaA bB bP rB rP zB zP H U := by
  unfold signedSourceLinear signedSourcePair
  rw [coefficientPair_add_right H T U bB rB zB zB,
      coefficientPair_add_right H T U bP rP zP zP,
      coefficientPair_add_left T U H bB rB zB zB,
      coefficientPair_add_left T U H bP rP zP zP]
  ring

theorem signedSourceLinear_scale_tail
    (alpha betaA : ℝ) (bB bP : Bool) (rB rP : ℕ)
    (zB : Fin rB → ℝ) (zP : Fin rP → ℝ)
    (H T : ℕ → ℂ) (a : ℂ) :
    signedSourceLinear alpha betaA bB bP rB rP zB zP H (fun k => a*T k) =
      a * signedSourceLinear alpha betaA bB bP rB rP zB zP H T := by
  unfold signedSourceLinear signedSourcePair
  rw [coefficientPair_scale_right a H T bB rB zB zB,
      coefficientPair_scale_right a H T bP rP zP zP,
      coefficientPair_scale_left a T H bB rB zB zB,
      coefficientPair_scale_left a T H bP rP zP zP]
  ring

/-- The exact HT+TH response is a linear functional of the original
shared source T. The quadratic TT is NOT included in this map. -/
def signedSourceLinearMap
    (alpha betaA : ℝ) (bB bP : Bool) (rB rP : ℕ)
    (zB : Fin rB → ℝ) (zP : Fin rP → ℝ)
    (H : ℕ → ℂ) : (ℕ → ℂ) →ₗ[ℂ] ℂ where
  toFun := signedSourceLinear alpha betaA bB bP rB rP zB zP H
  map_add' := signedSourceLinear_add_tail alpha betaA bB bP rB rP zB zP H
  map_smul' := by
    intro a T
    change signedSourceLinear alpha betaA bB bP rB rP zB zP H (fun k => a*T k) =
      a * signedSourceLinear alpha betaA bB bP rB rP zB zP H T
    exact signedSourceLinear_scale_tail alpha betaA bB bP rB rP zB zP H T a

def jetImpulse (j : ℕ) : ℕ → ℂ :=
  fun k => if k = j then 1 else 0

theorem prefixTail_eq_impulse_sum (N : ℕ) (T : ℕ → ℂ) :
    prefixTail N T =
      ∑ j : Fin N, (T j.val) • jetImpulse j.val := by
  funext k
  simp only [prefixTail, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hk : k < N
  · let j : Fin N := ⟨k,hk⟩
    have hsum : (∑ i : Fin N, T i.val * jetImpulse i.val k) =
       T k := by
      rw [Finset.sum_eq_single j]
      · simp [jetImpulse, j]
      · intro i hi hne
        have hneq : k ≠ i.val := by
          intro he
          apply hne
          apply Fin.ext
          exact he.symm
        simp [jetImpulse, hneq]
      · simp
    simp [hk, hsum]
  · simp only [if_neg hk]
    symm
    apply Finset.sum_eq_zero
    intro j hj
    have hne : k ≠ j.val := by
      intro he
      apply hk
      rw [he]
      exact j.isLt
    simp [jetImpulse,hne]

/-- The 23 impulse coefficients are uniquely determined by the original
signed source and shared head: each is the value at a unit jet impulse. -/
def signedImpulseCoefficient (N : ℕ)
    (alpha betaA : ℝ) (bB bP : Bool) (rB rP : ℕ)
    (zB : Fin rB → ℝ) (zP : Fin rP → ℝ)
    (H : ℕ → ℂ) (j : Fin N) : ℂ :=
  signedSourceLinear alpha betaA bB bP rB rP zB zP H
    (jetImpulse j.val)

/-- Replaces the old hCoeff hypothesis by a theorem. The cutoff is
derived from both source block sizes, not assigned by experiment. -/
theorem signed_linear_impulse_expansion
    (alpha betaA : ℝ) (bB bP : Bool) (rB rP N : ℕ)
    (zB : Fin rB → ℝ) (zP : Fin rP → ℝ)
    (H T : ℕ → ℂ) (hNB : 2*rB < N) (hNP : 2*rP < N) :
    signedSourceLinear alpha betaA bB bP rB rP zB zP H T =
      ∑ j : Fin N,
        signedImpulseCoefficient N alpha betaA bB bP rB rP zB zP H j * T j.val := by
  let L := signedSourceLinearMap alpha betaA bB bP rB rP zB zP H
  calc
    signedSourceLinear alpha betaA bB bP rB rP zB zP H T =
      L (prefixTail N T) :=
        signed_linear_prefixTail alpha betaA bB bP rB rP N zB zP H T hNB hNP
    _ = L (∑ j : Fin N, (T j.val) • jetImpulse j.val) := by
      rw [prefixTail_eq_impulse_sum]
    _ = ∑ j : Fin N,
        signedImpulseCoefficient N alpha betaA bB bP rB rP zB zP H j * T j.val := by
      simp only [map_sum, map_smul, smul_eq_mul, signedImpulseCoefficient]
      apply Finset.sum_congr rfl
      intro j _
      change T j.val * signedSourceLinear alpha betaA bB bP rB rP zB zP H (jetImpulse j.val) =
        signedSourceLinear alpha betaA bB bP rB rP zB zP H (jetImpulse j.val) * T j.val
      ring

end
end CarrySourceBezout
