import GeometryOfNumbers.Geometry.IntegerCameraIncidence
import GeometryOfNumbers.Analysis.CenterLegForm
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! A finite ledger of ACTUAL integer incidences and a quadratic readout.
Coefficients merge at the same integer, while camera/role labels remain in
the input family. The real plane and its coordinate energy are preexisting.
No Hilbert norm, target moment matrix, phase law or canonical field is chosen.
This synthesis energy is different from the existing sum of local energies. -/
namespace GeometryOfNumbers.Analysis
open Geometry
open scoped BigOperators
noncomputable section
set_option autoImplicit false

/-- The existing centered readout, sampled at the three ORIGINAL integers. -/
def integerCameraReadout (cell : IntegerCameraCell) (v : Int → RealPlaneState) :
    RealPlaneState :=
  realPlaneCenteredReadout (v (integerCameraPoint cell .left))
    (v (integerCameraPoint cell .center)) (v (integerCameraPoint cell .right))

/-- Signed point multiplicities of the existing stencil 1,-2,1. -/
def integerCellStencil (cell : IntegerCameraCell) : Int →₀ ℝ :=
  Finsupp.single (integerCameraPoint cell .left) 1 -
    Finsupp.single (integerCameraPoint cell .center) 2 +
    Finsupp.single (integerCameraPoint cell .right) 1

def integerIncidenceSynthesis (A : Int →₀ ℝ) (v : Int → RealPlaneState) : RealPlaneState :=
  Finsupp.linearCombination ℝ v A

/-- Explicit observation list and coefficients; no admissible partition is
silently supplied. The family still records every base, depth and role. -/
def integerIncidenceLedger {ι : Type*} (s : Finset ι)
    (cells : ι → IntegerCameraCell) (a : ι → ℝ) : Int →₀ ℝ :=
  ∑ i ∈ s, a i • integerCellStencil (cells i)

theorem integerCellStencil_synthesis (cell : IntegerCameraCell) (v : Int → RealPlaneState) :
    integerIncidenceSynthesis (integerCellStencil cell) v = integerCameraReadout cell v := by
  simp only [integerIncidenceSynthesis, integerCellStencil, map_add, map_sub,
    Finsupp.linearCombination_single, one_smul]
  apply Prod.ext <;> simp [integerCameraReadout, realPlaneCenteredReadout,
    realCenteredReadout]

/-- Reconstruction precedes the quadratic energy readout. -/
theorem integerIncidenceLedger_synthesis {ι : Type*} (s : Finset ι)
    (cells : ι → IntegerCameraCell) (a : ι → ℝ) (v : Int → RealPlaneState) :
    integerIncidenceSynthesis (integerIncidenceLedger s cells a) v =
      ∑ i ∈ s, a i • integerCameraReadout (cells i) v := by
  unfold integerIncidenceLedger
  change (Finsupp.linearCombination ℝ v) _ = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul]
  change a i • integerIncidenceSynthesis (integerCellStencil (cells i)) v = _
  rw [integerCellStencil_synthesis]

/-- Equality of the merged integer ledger is exactly equality of synthesis
for ALL point observations. A single observed field can conceal a defect. -/
theorem integerIncidenceSynthesis_ext_iff (A B : Int →₀ ℝ) :
    (∀ v : Int → RealPlaneState,
      integerIncidenceSynthesis A v = integerIncidenceSynthesis B v) ↔ A = B := by
  constructor
  · intro h
    apply Finsupp.ext
    intro n
    have hn := h (Pi.single n (1, 0))
    simp only [integerIncidenceSynthesis, Finsupp.linearCombination_single_index] at hn
    simpa using congrArg Prod.fst hn
  · intro h
    subst B
    intro v
    rfl

/-- Coordinate polarization of the existing energy, not another metric. -/
def integerObservationPair (u v : RealPlaneState) : ℝ := u.1 * v.1 + u.2 * v.2

theorem integerObservationPair_polarization (u v : RealPlaneState) :
    integerObservationPair u v =
      (realPlaneEnergy (u + v) - realPlaneEnergy u - realPlaneEnergy v) / 2 := by
  simp [integerObservationPair, realPlaneEnergy]
  ring

theorem integerIncidenceSynthesis_transport (A B : Int →₀ ℝ) (v : Int → RealPlaneState) :
    integerIncidenceSynthesis B v =
      integerIncidenceSynthesis A v + integerIncidenceSynthesis (B - A) v := by
  simp only [integerIncidenceSynthesis, map_sub]
  abel

/-- Two independent observations and BOTH ordered crosses survive. -/
theorem integerIncidence_pairing_transport (A B : Int →₀ ℝ)
    (v w : Int → RealPlaneState) :
    integerObservationPair (integerIncidenceSynthesis B v) (integerIncidenceSynthesis B w) -
        integerObservationPair (integerIncidenceSynthesis A v) (integerIncidenceSynthesis A w) =
      integerObservationPair (integerIncidenceSynthesis A v)
          (integerIncidenceSynthesis (B - A) w) +
        integerObservationPair (integerIncidenceSynthesis (B - A) v)
          (integerIncidenceSynthesis A w) +
        integerObservationPair (integerIncidenceSynthesis (B - A) v)
          (integerIncidenceSynthesis (B - A) w) := by
  rw [integerIncidenceSynthesis_transport A B v, integerIncidenceSynthesis_transport A B w]
  simp [integerObservationPair]
  ring

theorem integerIncidence_energy_transport (A B : Int →₀ ℝ) (v : Int → RealPlaneState) :
    realPlaneEnergy (integerIncidenceSynthesis B v) -
        realPlaneEnergy (integerIncidenceSynthesis A v) =
      2 * integerObservationPair (integerIncidenceSynthesis A v)
          (integerIncidenceSynthesis (B - A) v) +
        realPlaneEnergy (integerIncidenceSynthesis (B - A) v) := by
  rw [integerIncidenceSynthesis_transport A B v]
  simp [integerObservationPair, realPlaneEnergy]
  ring

/-- Exact condition for this field's conservation; neither sign nor zero of
the defect is imposed. This is weaker than equality of integer ledgers. -/
theorem integerIncidence_energy_conservation_iff (A B : Int →₀ ℝ)
    (v : Int → RealPlaneState) :
    realPlaneEnergy (integerIncidenceSynthesis B v) =
        realPlaneEnergy (integerIncidenceSynthesis A v) ↔
      2 * integerObservationPair (integerIncidenceSynthesis A v)
          (integerIncidenceSynthesis (B - A) v) +
        realPlaneEnergy (integerIncidenceSynthesis (B - A) v) = 0 := by
  rw [← integerIncidence_energy_transport, sub_eq_zero]

/-- The center shared by the two 72 cells occurs TWICE in the raw ledger. -/
theorem integerCamera72_center_multiplicity :
    (integerCellStencil integerCamera72Two + integerCellStencil integerCamera72Three) 72 = -4 ∧
      integerCellStencil integerCamera72Two ≠ integerCellStencil integerCamera72Three := by
  constructor
  · norm_num [integerCellStencil, integerCameraPoint, integerCameraCenter,
      integerCameraRadius, integerCamera72Two, integerCamera72Three, leftLeg, rightLeg]
  · intro h
    have hh := congrArg (fun A : Int →₀ ℝ => A 64) h
    norm_num [integerCellStencil, integerCameraPoint, integerCameraCenter,
      integerCameraRadius, integerCamera72Two, integerCamera72Three, leftLeg, rightLeg] at hh

/-- Finite sign freedom on actual integer points 63 and 64. The shared
center and all other points carry zero, consistently in both presentations. -/
def integerCamera72SignField (s : ℝ) (n : Int) : RealPlaneState :=
  if n = 64 then (1, 0) else if n = 63 then (s, 0) else (0, 0)

theorem integerCamera72_sign_field_local_energy (n : Int) :
    realPlaneEnergy (integerCamera72SignField 1 n) =
      realPlaneEnergy (integerCamera72SignField (-1) n) := by
  unfold integerCamera72SignField
  split_ifs <;> norm_num [realPlaneEnergy]

theorem integerCamera72_sign_field_readouts (s : ℝ) :
    integerCameraReadout integerCamera72Two (integerCamera72SignField s) = (1, 0) ∧
      integerCameraReadout integerCamera72Three (integerCamera72SignField s) = (s, 0) := by
  simp [integerCameraReadout, integerCamera72SignField, integerCameraPoint,
    integerCameraCenter, integerCameraRadius, integerCamera72Two, integerCamera72Three,
    leftLeg, rightLeg, realPlaneCenteredReadout, realCenteredReadout]

theorem integerCamera72_sign_field_synthesis (s : ℝ) :
    integerIncidenceSynthesis
      (integerCellStencil integerCamera72Two + integerCellStencil integerCamera72Three)
      (integerCamera72SignField s) = (1 + s, 0) := by
  change (Finsupp.linearCombination ℝ (integerCamera72SignField s)) _ = _
  rw [map_add]
  change integerIncidenceSynthesis (integerCellStencil integerCamera72Two) _ +
    integerIncidenceSynthesis (integerCellStencil integerCamera72Three) _ = _
  rw [integerCellStencil_synthesis, integerCellStencil_synthesis,
    (integerCamera72_sign_field_readouts s).1, (integerCamera72_sign_field_readouts s).2]
  simp

theorem integerCamera72_weighted_synthesis (a b s : ℝ) :
    integerIncidenceSynthesis
      (a • integerCellStencil integerCamera72Two + b • integerCellStencil integerCamera72Three)
      (integerCamera72SignField s) = (a + b * s, 0) := by
  change (Finsupp.linearCombination ℝ (integerCamera72SignField s)) _ = _
  rw [map_add, map_smul, map_smul]
  change a • integerIncidenceSynthesis (integerCellStencil integerCamera72Two) _ +
    b • integerIncidenceSynthesis (integerCellStencil integerCamera72Three) _ = _
  rw [integerCellStencil_synthesis, integerCellStencil_synthesis,
    (integerCamera72_sign_field_readouts s).1, (integerCamera72_sign_field_readouts s).2]
  simp

/-- Fixed arbitrary amplitudes do not remove the undetermined cross term. -/
theorem integerCamera72_weighted_energy_gap (a b : ℝ) :
    realPlaneEnergy (integerIncidenceSynthesis
      (a • integerCellStencil integerCamera72Two + b • integerCellStencil integerCamera72Three)
      (integerCamera72SignField 1)) -
    realPlaneEnergy (integerIncidenceSynthesis
      (a • integerCellStencil integerCamera72Two + b • integerCellStencil integerCamera72Three)
      (integerCamera72SignField (-1))) = 4 * a * b := by
  rw [integerCamera72_weighted_synthesis, integerCamera72_weighted_synthesis]
  dsimp only [realPlaneEnergy]
  ring

/-- Incidences, point energies AND individual cell-readout energies coincide;
the energy of their full synthesis differs (4 versus 0). Thus local data do
not fix the global polarized pairing, even at the actual two-camera overlap. -/
theorem integerCamera72_local_energy_does_not_determine_synthesis :
    (∀ n, realPlaneEnergy (integerCamera72SignField 1 n) =
      realPlaneEnergy (integerCamera72SignField (-1) n)) ∧
    (∀ cell ∈ ({integerCamera72Two, integerCamera72Three} : Finset IntegerCameraCell),
      realPlaneEnergy (integerCameraReadout cell (integerCamera72SignField 1)) =
        realPlaneEnergy (integerCameraReadout cell (integerCamera72SignField (-1)))) ∧
    realPlaneEnergy (integerIncidenceSynthesis
      (integerCellStencil integerCamera72Two + integerCellStencil integerCamera72Three)
      (integerCamera72SignField 1)) = 4 ∧
    realPlaneEnergy (integerIncidenceSynthesis
      (integerCellStencil integerCamera72Two + integerCellStencil integerCamera72Three)
      (integerCamera72SignField (-1))) = 0 := by
  refine ⟨integerCamera72_sign_field_local_energy, ?_, ?_, ?_⟩
  · intro cell hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl
    · rw [(integerCamera72_sign_field_readouts 1).1,
        (integerCamera72_sign_field_readouts (-1)).1]
    · rw [(integerCamera72_sign_field_readouts 1).2,
        (integerCamera72_sign_field_readouts (-1)).2]
      norm_num [realPlaneEnergy]
  all_goals
    rw [integerCamera72_sign_field_synthesis]
    norm_num [realPlaneEnergy]

end
end GeometryOfNumbers.Analysis
