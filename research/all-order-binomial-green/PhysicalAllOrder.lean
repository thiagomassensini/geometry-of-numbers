import JetFourSource
import StencilTransport

/-! The binomial law is attached to original physical jets after complete
vector synthesis. No Hilbert norm replaces the native signed Green pairing. -/
namespace CarryBinomialGreen
open CarryPolarizedFour CarryGreenFinitePart CarryInteriorGreen CarryFirstOddGreen CarryFiniteGreen
open CarryRadialGreen CarryMeanContrast CarryRadialRefinement CarryPhysicalTrace CarrySelfAdjointOperator
open CarrySelfAdjointOperator.NativeLaguerre
open scoped BigOperators ComplexConjugate InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- Original stencils, both parity sectors, arbitrary finite input. -/
def parityInput {N : ℕ} (s k : ℕ) (c : Fin N → ℝ) : ℕ →₀ ℂ :=
  ∑ j : Fin N, (c j:ℂ) • jetInput k (2*j.val+s)

theorem parity_source_original {N : ℕ} (s k : ℕ) (c : Fin N → ℝ) :
    completedSource k (parityInput s k c)=
      ∑ j : Fin N, (c j:ℂ) • physicalJet k (2*j.val+s) := by
  simp only [parityInput,map_sum,map_smul,jet_input_source]

theorem parity_input_even {N : ℕ} (k : ℕ) (c : Fin N → ℝ) :
    parityInput 0 k c=evenPolynomialInput k c := by
  simp only [parityInput,evenPolynomialInput,add_zero]

/-- The complete physical split holds before either argument is read out. -/
theorem parity_green_vector_split {N : ℕ} (s ηk : ℕ) (η : ℝ)
    (hη0 : 0<η) (hη1 : η<1) (c : Fin N → ℝ) :
    completedSource ηk (parityInput s ηk c)=
      reconstructedBulk 0 η ηk (parityInput s ηk c)+
      reconstructedResidual 0 η ηk (parityInput s ηk c) := by
  simpa only [pair_power_zero] using
    refined_source_green_split 0 η hη0 hη1 ηk (parityInput s ηk c)

/-- Four ordered sectors, independent inputs and arbitrary finite sizes. -/
theorem parity_green_four_sectors {N M : ℕ} (s r k : ℕ) (η : ℝ)
    (hη0 : 0<η) (hη1 : η<1) (c : Fin N → ℝ) (d : Fin M → ℝ) :
    physicalForm (completedSource k (parityInput s k c)) (completedSource k (parityInput r k d))=
    physicalForm (reconstructedBulk 0 η k (parityInput s k c)) (reconstructedBulk 0 η k (parityInput r k d))+
    physicalForm (reconstructedBulk 0 η k (parityInput s k c)) (reconstructedResidual 0 η k (parityInput r k d))+
    physicalForm (reconstructedResidual 0 η k (parityInput s k c)) (reconstructedBulk 0 η k (parityInput r k d))+
    physicalForm (reconstructedResidual 0 η k (parityInput s k c)) (reconstructedResidual 0 η k (parityInput r k d)) := by
  rw [parity_green_vector_split s k η hη0 hη1,
    parity_green_vector_split r k η hη0 hη1,physical_form_four_sectors]

/-- Every ordered cross is retained, with its original conjugate convention. -/
theorem parity_source_all_crosses {N M : ℕ} (s r k : ℕ)
    (c : Fin N → ℝ) (d : Fin M → ℝ) :
    physicalForm (completedSource k (parityInput s k c)) (completedSource k (parityInput r k d))=
      ∑ i : Fin N, ∑ j : Fin M, conj (c i:ℂ)*(d j:ℂ)*
        physicalForm (physicalJet k (2*i.val+s)) (physicalJet k (2*j.val+r)) := by
  rw [parity_source_original,parity_source_original,physical_form_sum]
  simp only [physical_form_smul]

end
end CarryBinomialGreen
