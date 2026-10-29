import ExactBalance

namespace CarryPolarizedFour
open CarryGreenFinitePart CarryInteriorGreen CarryFirstOddGreen CarryFiniteGreen CarryRadialGreen
open CarryMeanContrast CarryRadialRefinement CarryPhysicalTrace CarrySelfAdjointOperator
open CarrySelfAdjointOperator.NativeLaguerre Filter Topology
open scoped BigOperators ComplexConjugate InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000

/-- The original jet stencil, as an input to the pre-existing source map. -/
def jetInput (k p : ℕ) : ℕ →₀ ℂ :=
  (((p.factorial : ℂ)*canonicalCompletedC3RadialSecondStep k^p)⁻¹) •
    ∑ j ∈ Finset.range (p+1), completedGreenForwardWeight p j • basisInput j

theorem jet_input_source (k p : ℕ) : completedSource k (jetInput k p)=physicalJet k p := by
  simp only [jetInput,map_smul,map_sum,source_basis,physicalJet]

/-- Physical jets precede the coefficient choice, in every finite dimension. -/
def evenPolynomialInput {N : ℕ} (k : ℕ) (c : Fin N → ℝ) : ℕ →₀ ℂ :=
  ∑ j : Fin N, (c j : ℂ) • jetInput k (2*j.val)

theorem even_polynomial_source {N : ℕ} (k : ℕ) (c : Fin N → ℝ) :
    completedSource k (evenPolynomialInput k c)=
      ∑ j : Fin N, (c j : ℂ) • physicalJet k (2*j.val) := by
  simp only [evenPolynomialInput,map_sum,map_smul,jet_input_source]

def quarticInput (k : ℕ) (u : Fin 3 → ℝ) : ℕ →₀ ℂ :=
  evenPolynomialInput k u

theorem quartic_source_original (k : ℕ) (u : Fin 3 → ℝ) :
    completedSource k (quarticInput k u)=
      (u 2 : ℂ) • physicalJet k 4+(u 1 : ℂ) • physicalJet k 2+(u 0 : ℂ) • physicalJet k 0 := by
  rw [quarticInput,even_polynomial_source]
  norm_num [Fin.sum_univ_succ]
  module

def fourthScale (k : ℕ) : ℂ := ((24 : ℂ)*canonicalCompletedC3RadialSecondStep k^4)⁻¹

theorem fourth_scale_real (k : ℕ) : fourthScale k=((((k : ℝ)+1)^4/24 : ℝ) : ℂ) := by
  unfold fourthScale canonicalCompletedC3RadialSecondStep canonicalGreenJetStep
  push_cast
  have hk : (k : ℂ)+1≠0 := by exact_mod_cast (show (k : ℝ)+1≠0 by positivity)
  field_simp [hk,Complex.I_ne_zero]
  norm_num [Complex.I_sq]

def fiveWeight (k : ℕ) (u : Fin 3 → ℝ) : Fin 5 → ℝ :=
  ![u 0-u 1*((k : ℝ)+1)^2/2+u 2*((k : ℝ)+1)^4/24,
    u 1*((k : ℝ)+1)^2-u 2*((k : ℝ)+1)^4/6,
    -u 1*((k : ℝ)+1)^2/2+u 2*((k : ℝ)+1)^4/4,
    -u 2*((k : ℝ)+1)^4/6,u 2*((k : ℝ)+1)^4/24]

theorem quartic_input_five (k : ℕ) (u : Fin 3 → ℝ) :
    quarticInput k u=∑ j : Fin 5, (fiveWeight k u j : ℂ) • basisInput j := by
  have h2 : (((2 : ℂ)*canonicalCompletedC3RadialSecondStep k^2)⁻¹)=
      ((-((k : ℝ)+1)^2/2 : ℝ) : ℂ) := second_scale_real k
  have h4 : (((24 : ℂ)*canonicalCompletedC3RadialSecondStep k^4)⁻¹)=
      ((((k : ℝ)+1)^4/24 : ℝ) : ℂ) := fourth_scale_real k
  norm_num [quarticInput,evenPolynomialInput,Fin.sum_univ_succ,jetInput,
    Finset.sum_range_succ,completedGreenForwardWeight,Nat.choose] at h2 h4 ⊢
  rw [h2,h4]
  norm_num [fiveWeight]
  push_cast
  module

def fiveRegular (k : ℕ) : Prop := ∀ i : Fin 6,
  completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k i)≠0 ∧
  completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k i)≠0

theorem five_regular_eventually : ∀ᶠ k : ℕ in atTop, fiveRegular k := by
  filter_upwards [canonicalCompletedNativeRadialProjectiveChiral_eventually_regular 6] with k hk
  exact fun i => ⟨(hk i).2.1,(hk i).2.2⟩

theorem five_basis_residual (η : ℝ) (hη : η≠0) (k : ℕ) (hr : fiveRegular k) (j : Fin 5) :
    reconstructedResidual 0 η k (basisInput j)=
      (chiralRadialScale k • residualFeature η k j,chiralRadialScale k • residualFeature η k j) := by
  apply residual_basis_all η hη k j
  intro i hi
  exact hr ⟨i,by omega⟩

def quarticBulk (η : ℝ) (k : ℕ) (u : Fin 3 → ℝ) : PhysicalPair :=
  reconstructedBulk 0 η k (quarticInput k u)
def quarticResidual (η : ℝ) (k : ℕ) (u : Fin 3 → ℝ) : PhysicalPair :=
  reconstructedResidual 0 η k (quarticInput k u)

theorem quartic_bulk_five (η : ℝ) (hη0 : 0<η) (hη1 : η<1) (k : ℕ) (u : Fin 3 → ℝ) :
    quarticBulk η k u=∑ j : Fin 5, (fiveWeight k u j : ℂ) •
      reconstructedBulk 0 η k (basisInput j) := by
  unfold quarticBulk
  rw [← bulk_map_original η hη0 hη1,quartic_input_five,map_sum]
  simp only [map_smul]
  simp only [bulk_map_original η hη0 hη1]

theorem quartic_residual_five (η : ℝ) (k : ℕ) (u : Fin 3 → ℝ) :
    quarticResidual η k u=∑ j : Fin 5, (fiveWeight k u j : ℂ) •
      reconstructedResidual 0 η k (basisInput j) := by
  change residualMap η k (quarticInput k u)=_
  rw [quartic_input_five,map_sum]
  simp only [map_smul,residual_map_apply]

theorem quartic_vector_split (η : ℝ) (hη0 : 0<η) (hη1 : η<1) (k : ℕ) (u : Fin 3 → ℝ) :
    completedSource k (quarticInput k u)=quarticBulk η k u+quarticResidual η k u := by
  simpa only [pair_power_zero,quarticBulk,quarticResidual] using refined_source_green_split 0 η hη0 hη1 k (quarticInput k u)

/-- The full complex identity precedes the real scalar readout. -/
theorem quartic_full_green (η : ℝ) (hη0 : 0<η) (hη1 : η<1) (k : ℕ) (u v : Fin 3 → ℝ) :
    physicalForm (completedSource k (quarticInput k u)) (completedSource k (quarticInput k v))=
      physicalForm (quarticBulk η k u) (quarticBulk η k v)+
      physicalForm (quarticBulk η k u) (quarticResidual η k v)+
      physicalForm (quarticResidual η k u) (quarticBulk η k v)+
      physicalForm (quarticResidual η k u) (quarticResidual η k v) := by
  rw [quartic_vector_split η hη0 hη1,quartic_vector_split η hη0 hη1,physical_form_four_sectors]

theorem quartic_residual_cross_zero (η : ℝ) (hη : η≠0) (k : ℕ) (hr : fiveRegular k)
    (u v : Fin 3 → ℝ) : physicalForm (quarticResidual η k u) (quarticResidual η k v)=0 := by
  rw [quartic_residual_five,quartic_residual_five,physical_form_sum]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  rw [physical_form_smul,five_basis_residual η hη k hr i,five_basis_residual η hη k hr j]
  simp only [physicalForm,sub_self,mul_zero]

/-- All 25 ORDERED mixed crosses, with conjugation, before scalarization. -/
theorem quartic_mixed_twenty_five (η : ℝ) (hη0 : 0<η) (hη1 : η<1) (k : ℕ)
    (u v : Fin 3 → ℝ) : physicalForm (quarticBulk η k u) (quarticResidual η k v)=
      ∑ i : Fin 5, ∑ j : Fin 5, conj (fiveWeight k u i : ℂ)*(fiveWeight k v j : ℂ)*
        physicalForm (reconstructedBulk 0 η k (basisInput i))
          (reconstructedResidual 0 η k (basisInput j)) := by
  rw [quartic_bulk_five η hη0 hη1,quartic_residual_five,physical_form_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact physical_form_smul _ _ _ _

end
end CarryPolarizedFour
