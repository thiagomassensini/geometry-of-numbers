import CommonKernel
import CarrySelfAdjointOperator.CompletedNativeProjectiveChiralForwardDifference

namespace CarryRadialRefinement
open CarryPhysicalTrace CarryCompletedTrace CarrySelfAdjointOperator
open CarrySelfAdjointOperator.NativeLaguerre Filter Topology
open scoped BigOperators ComplexConjugate InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

abbrev PhysicalPair := PhysicalCauchySpace × PhysicalCauchySpace

def physicalForm (u v : PhysicalPair) : ℂ :=
  (2 : ℂ)⁻¹*(inner ℂ u.1 v.1-inner ℂ u.2 v.2)

def physicalJet (k p : ℕ) : PhysicalPair :=
  (((p.factorial : ℂ)*canonicalCompletedC3RadialSecondStep k^p)⁻¹) •
    ∑ r ∈ Finset.range (p+1), completedGreenForwardWeight p r • projectiveLegs k r

def commonJetPairing (k l p q : ℕ) : ℂ :=
  physicalForm (pairPower l (physicalJet k p)) (pairPower k (physicalJet l q))

theorem physical_form_smul (c d : ℂ) (u v : PhysicalPair) :
    physicalForm (c • u) (d • v) = conj c*d*physicalForm u v := by
  simp only [physicalForm,Prod.smul_fst,Prod.smul_snd,
    _root_.inner_smul_left (𝕜 := ℂ) (E := PhysicalCauchySpace),
    _root_.inner_smul_right (𝕜 := ℂ) (E := PhysicalCauchySpace)]
  ring

theorem physical_form_sum {ι ι' : Type*} (s : Finset ι) (t : Finset ι')
    (u : ι → PhysicalPair) (v : ι' → PhysicalPair) :
    physicalForm (∑ i ∈ s,u i) (∑ j ∈ t,v j) =
      ∑ i ∈ s,∑ j ∈ t,physicalForm (u i) (v j) := by
  have hfu : (∑ i ∈ s,u i).1 = ∑ i ∈ s,(u i).1 := map_sum (AddMonoidHom.fst _ _) u s
  have hfv : (∑ j ∈ t,v j).1 = ∑ j ∈ t,(v j).1 := map_sum (AddMonoidHom.fst _ _) v t
  have hsu : (∑ i ∈ s,u i).2 = ∑ i ∈ s,(u i).2 := map_sum (AddMonoidHom.snd _ _) u s
  have hsv : (∑ j ∈ t,v j).2 = ∑ j ∈ t,(v j).2 := map_sum (AddMonoidHom.snd _ _) v t
  simp only [physicalForm,hfu,hfv,hsu,hsv,sum_inner,inner_sum]
  rw [Finset.sum_comm (f := fun j i => inner ℂ (u i).1 (v j).1),
    Finset.sum_comm (f := fun j i => inner ℂ (u i).2 (v j).2)]
  simp only [mul_sub,Finset.mul_sum,Finset.sum_sub_distrib]

def ambientPair : PhysicalPair →ₗ[ℂ] CanonicalCompletedNativeProjectiveChiralCarrier where
  toFun u := (u.1.val,u.2.val)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem ambient_projective_legs (k j : ℕ) :
    ambientPair (projectiveLegs k j) = canonicalCompletedNativeRadialProjectiveChiralState k j :=
  projective_legs_original k j

/-- Exact original vector identity, before any signed scalar readout. -/
theorem physical_jet_original (k p : ℕ) :
    ((physicalJet k p).1.val,(physicalJet k p).2.val) = projectiveChiralDifferenceJet k p := by
  change ambientPair (physicalJet k p) = _
  simp only [physicalJet,map_smul,map_sum,ambient_projective_legs]
  rfl

/-- Two separate finite differences, with all ordered crosses. -/
theorem common_jet_pairing_weighted (k l p q : ℕ) : commonJetPairing k l p q =
    conj (((p.factorial : ℂ)*canonicalCompletedC3RadialSecondStep k^p)⁻¹) *
    (((q.factorial : ℂ)*canonicalCompletedC3RadialSecondStep l^q)⁻¹) *
    ∑ i ∈ Finset.range (p+1),∑ j ∈ Finset.range (q+1),
      completedGreenForwardWeight p i*completedGreenForwardWeight q j*commonPairing k l i j := by
  unfold commonJetPairing physicalJet
  simp only [map_smul,map_sum]
  rw [physical_form_smul,physical_form_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [physical_form_smul]
  have hc : conj (completedGreenForwardWeight p i) = completedGreenForwardWeight p i := by
    simp [completedGreenForwardWeight]
  rw [hc]
  rfl

/-- The exact native shifted difference now holds with TWO radial indices. -/
theorem common_jet_pairing_dslope (k l p q : ℕ)
    (hk : ∀ i : Fin (p+q+1), canonicalCompletedC3RadialTiltPoint k i ∈ completedNativeHeightDomain ∧
      completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k i) ≠ 0 ∧
      completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k i) ≠ 0)
    (hl : ∀ i : Fin (p+q+1), canonicalCompletedC3RadialTiltPoint l i ∈ completedNativeHeightDomain ∧
      completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint l i) ≠ 0 ∧
      completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint l i) ≠ 0) :
    commonJetPairing k l p q = completedGreenKernelTwoStepShiftedForwardDifference
      canonicalCompletedNativePolarizedDslopeKernel
      (canonicalCompletedC3RadialSecondStep k) (canonicalCompletedC3RadialSecondStep l) p q := by
  rw [common_jet_pairing_weighted]
  unfold completedGreenKernelTwoStepShiftedForwardDifference
    completedGreenKernelTwoStepShiftedRawDifference
  congr 1
  rw [completedGreenForwardDifference_iter_eq_sum_shift]
  apply Finset.sum_congr rfl
  intro i hi
  rw [completedGreenForwardDifference_iter_eq_sum_shift]
  simp only [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hi' : i < p+q+1 := by have := Finset.mem_range.mp hi; omega
  have hj' : j < p+q+1 := by have := Finset.mem_range.mp hj; omega
  rw [common_pairing_kernel k l i j (hk ⟨i,hi'⟩).1 (hk ⟨i,hi'⟩).2.1
    (hl ⟨j,hj'⟩).2.1 (hk ⟨i,hi'⟩).2.2 (hl ⟨j,hj'⟩).2.2,
    canonicalCompletedC3RadialTiltPoint_eq_step_add_nsmul,
    canonicalCompletedC3RadialTiltPoint_eq_step_add_nsmul]
  simp [completedGreenForwardWeight,zsmul_eq_mul]
  ring

/-- No source regularity is postulated globally; the original germ discharges
it eventually, independently in both variables. -/
theorem common_jet_pairing_eventually_dslope (p q : ℕ) :
    (fun steps : ℕ × ℕ => commonJetPairing steps.1 steps.2 p q) =ᶠ[atTop]
    (fun steps => completedGreenKernelTwoStepShiftedForwardDifference
      canonicalCompletedNativePolarizedDslopeKernel
      (canonicalCompletedC3RadialSecondStep steps.1)
      (canonicalCompletedC3RadialSecondStep steps.2) p q) := by
  have hf : Tendsto (Prod.fst : ℕ × ℕ → ℕ) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_fst
  have hs : Tendsto (Prod.snd : ℕ × ℕ → ℕ) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_snd
  have hr := canonicalCompletedNativeRadialProjectiveChiral_eventually_regular (p+q+1)
  filter_upwards [hf.eventually hr,hs.eventually hr] with steps hk hl
  exact common_jet_pairing_dslope _ _ p q hk hl

/-- All orders: the original physical jets, after the proved isometric common
refinement, have the canonical JOINT signed coefficient limit. -/
theorem common_jet_pairing_tendsto (p q : ℕ) :
    Tendsto (fun steps : ℕ × ℕ => commonJetPairing steps.1 steps.2 p q) atTop
      (nhds (polarizedGreenMomentCoefficient canonicalCompletedNativeLogDerivativeMoment p q)) :=
  (completedNativePolarizedDslope_shiftedRadial_tendsto p q).congr'
    (common_jet_pairing_eventually_dslope p q).symm

theorem common_even_jets (i j : ℕ) :
    Tendsto (fun steps : ℕ × ℕ => commonJetPairing steps.1 steps.2 (2*i) (2*j)) atTop
      (nhds (canonicalCompletedNativeLogDerivativeMoment (i+j) : ℂ)) := by
  simpa only [polarizedGreenMomentCoefficient_even_even] using common_jet_pairing_tendsto (2*i) (2*j)

theorem common_odd_jets (i j : ℕ) :
    Tendsto (fun steps : ℕ × ℕ => commonJetPairing steps.1 steps.2 (2*i+1) (2*j+1)) atTop
      (nhds (canonicalCompletedNativeLogDerivativeMoment (i+j+1) : ℂ)) := by
  simpa only [polarizedGreenMomentCoefficient_odd_odd] using common_jet_pairing_tendsto (2*i+1) (2*j+1)

theorem common_even_odd_jets (i j : ℕ) :
    Tendsto (fun steps : ℕ × ℕ => commonJetPairing steps.1 steps.2 (2*i) (2*j+1)) atTop (nhds (0 : ℂ)) := by
  simpa only [polarizedGreenMomentCoefficient_even_odd] using common_jet_pairing_tendsto (2*i) (2*j+1)

end
end CarryRadialRefinement
