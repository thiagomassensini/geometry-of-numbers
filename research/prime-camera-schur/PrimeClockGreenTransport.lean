import PrimeClockCanonicalGate

/-! Feed the coherently completed prime clock into the existing companion,
dressing and Green reduction. This reaches the SIGNED canonical residual
ledger; it does not turn the Green difference into a positive inner product. -/
namespace CarryPrimeClock
open GeometryOfNumbers.Analysis GeometryOfNumbers.Analysis.BaseTwoCompletion
open CarryMaterialGreenPairComparison CarryMaterialPositiveResidualComparison
open scoped InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

def primeCompanionValuePair (M : ℕ) (t : ℝ) : MaterialCarrier × MaterialCarrier :=
  (-(baseTwoCanonicalDressingScalar t •
      (-Complex.I • (physicalClockHead M t + physicalClockTail M t)) +
      deriv baseTwoCanonicalDressingScalar t • baseTwoCompletedBoundaryHilbertState t),
   (2:ℂ) • baseTwoVectorDressing t (baseTwoCompletedBoundaryHilbertState t))

/-- The derivative of dressing acts on the full value. Both seed and
ordinary return remain in that value; the clocked return is separate. -/
theorem primeCompanionValuePair_eq (M : ℕ) (t : ℝ) :
    primeCompanionValuePair M t = carryMaterialCompanionValuePair t := by
  rw [primeCompanionValuePair, physicalClock_head_tail]
  rfl

def primeReducedPair (M : ℕ) (t : ℝ) : MaterialCarrier × MaterialCarrier :=
  carryMaterialPairReduction t (primeCompanionValuePair M t)

theorem primeReducedPair_eq (M : ℕ) (t : ℝ) :
    primeReducedPair M t = carryMaterialReducedCompanionPair t := by
  rw [primeReducedPair, primeCompanionValuePair_eq]
  rfl

/-- Source-built prime coordinates reach the canonical REAL residual
numerator. Cutoffs and parameters are independent; no denominator is divided
out, including on t=0, u=0 or t=u. The hidden Green term is retained. -/
theorem completed_prime_green_real_residual :
    ∃ U : Set ℝ, IsOpen U ∧ (0:ℝ) ∈ U ∧
      ∀ (M N : ℕ), ∀ t ∈ U, ∀ u ∈ U,
        carryMaterialPairGreen (primeReducedPair M t) (primeReducedPair N u) -
          carryMaterialPairGreen (carryMaterialPairComplement (primeReducedPair M t))
            (carryMaterialPairComplement (primeReducedPair N u)) =
          (2:ℂ)*((carryMaterialResponseScale^2*t*u:ℝ):ℂ)*
            conj (baseTwoCanonicalResponse t)*baseTwoCanonicalResponse u*((u-t:ℝ):ℂ)*
              (carryMaterialRealResidual t u:ℂ) := by
  obtain ⟨U,ho,hz,h⟩ := material_reduced_pair_canonical_residual_numerator
  refine ⟨U,ho,hz,?_⟩
  intro M N t ht u hu
  rw [primeReducedPair_eq, primeReducedPair_eq, material_real_residual_coe]
  exact h t ht u hu

end
end CarryPrimeClock
