import GreenIntertwiner
import CommonJets

/-! Whole original finite TFVD source, two boundary ports and analytic residual.
All are transported as vectors before signed pairing. -/
namespace CarryRadialGreen
open CarryPhysicalTrace CarryRadialRefinement CarrySelfAdjointOperator
open CarrySelfAdjointOperator.NativeLaguerre CarrySelfAdjointOperator.NativeCauchyPorts
open CarrySelfAdjointOperator.FirstEdgeSewing
open scoped BigOperators ComplexConjugate InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

def pairAdvance : PhysicalPair →L[ℂ] PhysicalPair := nativeAdvance.prodMap nativeAdvance
def pairResolvent (r : ℕ) (η : ℝ) : PhysicalPair →L[ℂ] PhysicalPair :=
  (greenResolvent r η).prodMap (greenResolvent r η)

theorem ambient_pair_injective : Function.Injective ambientPair := by
  intro x y h
  apply Prod.ext
  · apply Subtype.ext; exact congrArg Prod.fst h
  · apply Subtype.ext; exact congrArg Prod.snd h

theorem ambient_pair_advance (x : PhysicalPair) :
    ambientPair (pairAdvance x) = physicalPairRadialAdvance (ambientPair x) := rfl

theorem ambient_pair_resolvent (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1) (x : PhysicalPair) :
    ambientPair (pairResolvent 1 η x) = physicalPairGreenResolvent η hη0 hη1 (ambientPair x) := by
  apply Prod.ext
  · exact green_resolvent_one_original η hη0 hη1 x.1
  · exact green_resolvent_one_original η hη0 hη1 x.2

theorem ambient_pair_resolvent_squared (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1) (x : PhysicalPair) :
    ambientPair (((pairResolvent 1 η)^2) x) =
      ((physicalPairGreenResolvent η hη0 hη1)^2) (ambientPair x) := by
  simp only [pow_two,mul_apply_eq_comp,ambient_pair_resolvent η hη0 hη1]

def completedSource (k : ℕ) : (ℕ →₀ ℂ) →ₗ[ℂ] PhysicalPair :=
  Finsupp.linearCombination ℂ (projectiveLegs k)

theorem completed_source_original (k : ℕ) (x : ℕ →₀ ℂ) :
    ambientPair (completedSource k x) = physicalCompletedFiniteSource k x := by
  rw [physicalCompletedFiniteSource_original]
  simp only [completedSource,Finsupp.linearCombination_apply,Finsupp.sum,map_sum,map_smul,ambient_projective_legs]

def completedResidual (k : ℕ) (x : ℕ →₀ ℂ) : PhysicalPair :=
  completedSource k (coefficientShift x)-pairAdvance (completedSource k x)

theorem completed_residual_original (k : ℕ) (x : ℕ →₀ ℂ) :
    ambientPair (completedResidual k x) = physicalCompletedFiniteResidual k x := by
  have h := congrArg continuousPairToSource (completedFiniteSynthesis_shift k x)
  simp only [map_add,continuousPairToSource_physical_advance] at h
  change physicalCompletedFiniteSource k (coefficientShift x) =
    physicalPairRadialAdvance (physicalCompletedFiniteSource k x)+physicalCompletedFiniteResidual k x at h
  rw [completedResidual,map_sub,ambient_pair_advance,completed_source_original,completed_source_original,h]
  abel

def bulkBoundary (η : ℝ) (k : ℕ) (x : ℕ →₀ ℂ) : PhysicalPair :=
  pairAdvance (completedSource k (finiteTfvdBulk η x))+
    ((η : ℂ)⁻¹*finiteTrace0 x) • projectiveLegs k 0+
    (finiteTrace1 η x-finiteTrace0 x) • projectiveLegs k 1

def residualNumerator (η : ℝ) (k : ℕ) (x : ℕ →₀ ℂ) : PhysicalPair :=
  completedResidual k (finiteTfvdBulk η x)+(2 : ℂ) • completedResidual k x-
    (η : ℂ) • (pairAdvance (completedResidual k x)+completedResidual k (coefficientShift x))

theorem bulk_boundary_original (η : ℝ) (k : ℕ) (x : ℕ →₀ ℂ) :
    ambientPair (bulkBoundary η k x) = physicalGreenBulkBoundary η k x := by
  simp only [bulkBoundary,physicalGreenBulkBoundary,map_add,map_smul,ambient_pair_advance,
    completed_source_original,ambient_projective_legs]

theorem residual_numerator_original (η : ℝ) (k : ℕ) (x : ℕ →₀ ℂ) :
    ambientPair (residualNumerator η k x) = physicalGreenResidualNumerator η k x := by
  simp only [residualNumerator,physicalGreenResidualNumerator,map_sub,map_add,map_smul,
    ambient_pair_advance,completed_residual_original]

/-- The old numerator identity in its actual closed physical source domain. -/
theorem completed_numerator (η : ℝ) (k : ℕ) (x : ℕ →₀ ℂ) :
    (η : ℂ)⁻¹ • completedSource k x-(2 : ℂ) • pairAdvance (completedSource k x)+
      (η : ℂ) • pairAdvance (pairAdvance (completedSource k x)) =
    bulkBoundary η k x+residualNumerator η k x := by
  apply ambient_pair_injective
  simp only [map_sub,map_add,map_smul,ambient_pair_advance,completed_source_original,
    bulk_boundary_original,residual_numerator_original]
  exact physicalCompletedFiniteGreen_numerator η k x

/-- Equality with the original corrected Green reconstruction, with both
trace ports and every residual term, before any scalar readout. -/
theorem completed_reconstruct (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1)
    (k : ℕ) (x : ℕ →₀ ℂ) : completedSource k x =
    (η : ℂ) • ((pairResolvent 1 η)^2) (bulkBoundary η k x+residualNumerator η k x) := by
  apply ambient_pair_injective
  simp only [map_smul,completed_source_original,ambient_pair_resolvent_squared η hη0.le hη1,
    map_add,bulk_boundary_original,residual_numerator_original]
  simpa only [map_add] using physicalCompletedFiniteGreen_reconstruct η hη0 hη1 k x

theorem pair_power_resolvent (m : ℕ) (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1) (x : PhysicalPair) :
    pairPower m (pairResolvent 1 η x) = pairResolvent (m+1) η (pairPower m x) := by
  apply Prod.ext
  · exact power_green_resolvent m η hη0 hη1 x.1
  · exact power_green_resolvent m η hη0 hη1 x.2

theorem pair_power_resolvent_squared (m : ℕ) (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1) (x : PhysicalPair) :
    pairPower m (((pairResolvent 1 η)^2) x) = ((pairResolvent (m+1) η)^2) (pairPower m x) := by
  simp only [pow_two,mul_apply_eq_comp,pair_power_resolvent m η hη0 hη1]

/-- Full TFVD/Green intertwining. The analytic residual is carried, not killed. -/
theorem refined_completed_reconstruct (m : ℕ) (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1)
    (k : ℕ) (x : ℕ →₀ ℂ) : pairPower m (completedSource k x) =
    (η : ℂ) • ((pairResolvent (m+1) η)^2)
      (pairPower m (bulkBoundary η k x)+pairPower m (residualNumerator η k x)) := by
  rw [completed_reconstruct η hη0 hη1 k x,map_smul,pair_power_resolvent_squared m η hη0.le hη1,map_add]

theorem physical_form_four_sectors (u v w z : PhysicalPair) :
    physicalForm (u+v) (w+z) = physicalForm u w+physicalForm u z+
      physicalForm v w+physicalForm v z := by
  simp only [physicalForm,Prod.fst_add,Prod.snd_add,inner_add_left,inner_add_right]
  ring

/-- Independent refinements AND original source inputs: BB, BR, RB, RR all survive. -/
theorem refined_completed_four_sectors (m n : ℕ) (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1)
    (k l : ℕ) (x y : ℕ →₀ ℂ) :
    let W := fun a z => (η : ℂ) • ((pairResolvent (a+1) η)^2) (pairPower a z)
    physicalForm (pairPower m (completedSource k x)) (pairPower n (completedSource l y)) =
    physicalForm (W m (bulkBoundary η k x)) (W n (bulkBoundary η l y))+
    physicalForm (W m (bulkBoundary η k x)) (W n (residualNumerator η l y))+
    physicalForm (W m (residualNumerator η k x)) (W n (bulkBoundary η l y))+
    physicalForm (W m (residualNumerator η k x)) (W n (residualNumerator η l y)) := by
  dsimp only
  rw [refined_completed_reconstruct m η hη0 hη1 k x,
    refined_completed_reconstruct n η hη0 hη1 l y]
  simp only [map_add,smul_add]
  exact physical_form_four_sectors _ _ _ _

end
end CarryRadialGreen
