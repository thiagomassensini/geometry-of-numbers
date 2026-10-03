import GeometryOfNumbers.Analysis.RealCarryTfvd
import GeometryOfNumbers.Analysis.SynthesizedPhaseCenterLegCanary
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Module

/-!
# Real material log orbit and pointwise TFVD lift

`n : Fin N` labels material fibers; `k : Nat` labels vertical coordinates.
The log clock uses only n.val. R2 is unchanged. This canary is a finite family
of its vertical carrier, not an identification with a historical source state.
No independent angles are inputs of the evolution.
-/

namespace GeometryOfNumbers.Analysis

noncomputable section

open RealCarry
open scoped BigOperators

def materialLogAngle (t : ℝ) (n : ℕ) : ℝ :=
  -(t * Real.log ((n + 1 : ℕ) : ℝ))

def materialLogRotate (t : ℝ) (n : ℕ) (v : RealPlaneState) : RealPlaneState :=
  rotateRealPlane (materialLogAngle t n) v

theorem materialLogRotate_zero (n : ℕ) (v : RealPlaneState) :
    materialLogRotate 0 n v = v := by
  simp [materialLogRotate, materialLogAngle, rotateRealPlane_zero]

theorem materialLogRotate_add (t s : ℝ) (n : ℕ) (v : RealPlaneState) :
    materialLogRotate (t + s) n v =
      materialLogRotate t n (materialLogRotate s n v) := by
  have h : materialLogAngle (t + s) n = materialLogAngle t n + materialLogAngle s n := by
    unfold materialLogAngle
    ring
  exact (congrArg (fun a => rotateRealPlane a v) h).trans (rotateRealPlane_add _ _ _)

theorem materialLogRotate_energy (t : ℝ) (n : ℕ) (v : RealPlaneState) :
    realPlaneEnergy (materialLogRotate t n v) = realPlaneEnergy v :=
  rotateRealPlane_energy _ _

theorem materialLogRotate_neg_comp (t : ℝ) (n : ℕ) (v : RealPlaneState) :
    materialLogRotate (-t) n (materialLogRotate t n v) = v := by
  rw [← materialLogRotate_add, neg_add_cancel, materialLogRotate_zero]

theorem materialLogRotate_eq_zero_iff (t : ℝ) (n : ℕ) (v : RealPlaneState) :
    materialLogRotate t n v = (0, 0) ↔ v = (0, 0) :=
  rotateRealPlane_eq_zero_iff _ _

section Quadratures

variable {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F]

/-- Two real quadratures; the same angle acts on the entire vertical fiber. -/
def realQuadratureRotate (theta : ℝ) (v : E × E) : E × E :=
  (Real.cos theta • v.1 - Real.sin theta • v.2,
    Real.sin theta • v.1 + Real.cos theta • v.2)

def realQuadratureMap (L : E →ₗ[ℝ] F) (v : E × E) : F × F :=
  (L v.1, L v.2)

theorem realQuadratureRotate_zero (v : E × E) : realQuadratureRotate 0 v = v := by
  simp [realQuadratureRotate]

theorem realQuadratureRotate_add (theta phi : ℝ) (v : E × E) :
    realQuadratureRotate (theta + phi) v =
      realQuadratureRotate theta (realQuadratureRotate phi v) := by
  apply Prod.ext <;>
    simp only [realQuadratureRotate, Real.cos_add, Real.sin_add] <;> module

theorem realQuadratureRotate_neg_comp (theta : ℝ) (v : E × E) :
    realQuadratureRotate (-theta) (realQuadratureRotate theta v) = v := by
  rw [← realQuadratureRotate_add, neg_add_cancel, realQuadratureRotate_zero]

theorem realQuadratureRotate_eq_zero_iff (theta : ℝ) (v : E × E) :
    realQuadratureRotate theta v = 0 ↔ v = 0 := by
  constructor
  · intro h
    have hi := realQuadratureRotate_neg_comp theta v
    rw [h] at hi
    change v = (0, 0)
    simpa [realQuadratureRotate] using hi.symm
  · intro h
    simp [h, realQuadratureRotate]

/-- Naturality uses only real linearity, including all boundary coordinates. -/
theorem realQuadratureMap_rotate (L : E →ₗ[ℝ] F) (theta : ℝ) (v : E × E) :
    realQuadratureMap L (realQuadratureRotate theta v) =
      realQuadratureRotate theta (realQuadratureMap L v) := by
  apply Prod.ext <;> simp [realQuadratureMap, realQuadratureRotate]

/-- One global t; material labels remain arguments of the fixed clock. -/
def materialLogPhase {N : ℕ} (t : ℝ) (X : Fin N → E × E) : Fin N → E × E :=
  fun n => realQuadratureRotate (materialLogAngle t n.val) (X n)

theorem materialLogPhase_zero {N : ℕ} (X : Fin N → E × E) :
    materialLogPhase 0 X = X := by
  funext n
  simp [materialLogPhase, materialLogAngle, realQuadratureRotate_zero]

theorem materialLogPhase_add {N : ℕ} (t s : ℝ) (X : Fin N → E × E) :
    materialLogPhase (t + s) X = materialLogPhase t (materialLogPhase s X) := by
  funext n
  have h : materialLogAngle (t + s) n.val =
      materialLogAngle t n.val + materialLogAngle s n.val := by
    unfold materialLogAngle
    ring
  simp only [materialLogPhase, h, realQuadratureRotate_add]

theorem materialLogPhase_neg_comp {N : ℕ} (t : ℝ) (X : Fin N → E × E) :
    materialLogPhase (-t) (materialLogPhase t X) = X := by
  rw [← materialLogPhase_add, neg_add_cancel, materialLogPhase_zero]

theorem materialLogPhase_eq_zero_iff {N : ℕ} (t : ℝ) (X : Fin N → E × E) :
    materialLogPhase t X = 0 ↔ X = 0 := by
  constructor
  · intro h
    funext n
    have hn := congrFun h n
    change realQuadratureRotate (materialLogAngle t n.val) (X n) = 0 at hn
    exact (realQuadratureRotate_eq_zero_iff _ _).mp hn
  · intro h
    subst X
    funext n
    change realQuadratureRotate _ (0, 0) = (0, 0)
    simp [realQuadratureRotate]

end Quadratures

theorem realQuadratureRotate_eq_rotateRealPlane (theta : ℝ) (v : RealPlaneState) :
    realQuadratureRotate theta v = rotateRealPlane theta v := by
  apply Prod.ext <;> simp only [realQuadratureRotate, rotateRealPlane, smul_eq_mul] <;> ring

abbrev MaterialVerticalCarrier (N : ℕ) := Fin N → (CarryVerticalL2 × CarryVerticalL2)

abbrev MaterialVerticalAnalysisCarrier (N : ℕ) :=
  Fin N → ((CarryVerticalL2 × (ℝ × ℝ)) × (CarryVerticalL2 × (ℝ × ℝ)))

def materialTfvdAnalysis {N : ℕ} (eta : ℝ) (X : MaterialVerticalCarrier N) :
    MaterialVerticalAnalysisCarrier N :=
  fun n => realQuadratureMap (realCarryTfvdAnalysis eta).toLinearMap (X n)

def materialTfvdSynthesis {N : ℕ} (eta : ℝ) (h0 : 0 ≤ eta) (h1 : eta < 1)
    (Y : MaterialVerticalAnalysisCarrier N) : MaterialVerticalCarrier N :=
  fun n => realQuadratureMap (realCarryTfvdSynthesis eta h0 h1).toLinearMap (Y n)

theorem materialTfvdSynthesis_comp_analysis {N : ℕ} (eta : ℝ)
    (h0 : 0 < eta) (h1 : eta < 1) (X : MaterialVerticalCarrier N) :
    materialTfvdSynthesis eta h0.le h1 (materialTfvdAnalysis eta X) = X := by
  have hr (x : CarryVerticalL2) :
      realCarryTfvdSynthesis eta h0.le h1 (realCarryTfvdAnalysis eta x) = x := by
    simpa using congrArg (fun L : CarryVerticalL2 →L[ℝ] CarryVerticalL2 => L x)
      (realCarryTfvdSynthesis_comp_analysis eta h0 h1)
  funext n
  apply Prod.ext <;> exact hr _

theorem materialTfvdAnalysis_phase {N : ℕ} (eta t : ℝ) (X : MaterialVerticalCarrier N) :
    materialTfvdAnalysis eta (materialLogPhase t X) =
      materialLogPhase t (materialTfvdAnalysis eta X) := by
  funext n
  exact realQuadratureMap_rotate _ _ _

theorem materialTfvdSynthesis_phase {N : ℕ} (eta : ℝ) (h0 : 0 ≤ eta) (h1 : eta < 1)
    (t : ℝ) (Y : MaterialVerticalAnalysisCarrier N) :
    materialTfvdSynthesis eta h0 h1 (materialLogPhase t Y) =
      materialLogPhase t (materialTfvdSynthesis eta h0 h1 Y) := by
  funext n
  exact realQuadratureMap_rotate _ _ _

theorem materialTfvdSynthesis_phase_zero_iff {N : ℕ} (eta : ℝ)
    (h0 : 0 ≤ eta) (h1 : eta < 1) (t : ℝ) (Y : MaterialVerticalAnalysisCarrier N) :
    materialTfvdSynthesis eta h0 h1 (materialLogPhase t Y) = 0 ↔
      materialTfvdSynthesis eta h0 h1 Y = 0 := by
  rw [materialTfvdSynthesis_phase, materialLogPhase_eq_zero_iff]

/-- Synthesis after evolving the analysis data is the log orbit of the original
state. This uses the existing R2 roundtrip, not a new reconstruction argument. -/
theorem materialTfvdSynthesized_logOrbit {N : ℕ} (eta : ℝ)
    (h0 : 0 < eta) (h1 : eta < 1) (t : ℝ) (X : MaterialVerticalCarrier N) :
    materialTfvdSynthesis eta h0.le h1
        (materialLogPhase t (materialTfvdAnalysis eta X)) = materialLogPhase t X := by
  rw [materialTfvdSynthesis_phase, materialTfvdSynthesis_comp_analysis eta h0 h1]

/-- Canonical coordinate evaluation; n and k are separate arguments. -/
def materialVerticalPlaneAt {N : ℕ} (X : MaterialVerticalCarrier N)
    (n : Fin N) (k : ℕ) : RealPlaneState := ((X n).1 k, (X n).2 k)

theorem materialLogPhase_planeAt {N : ℕ} (t : ℝ) (X : MaterialVerticalCarrier N)
    (n : Fin N) (k : ℕ) :
    materialVerticalPlaneAt (materialLogPhase t X) n k =
      materialLogRotate t n.val (materialVerticalPlaneAt X n k) := by
  change realQuadratureMap (carryVerticalL2Eval k).toLinearMap
      (realQuadratureRotate (materialLogAngle t n.val) (X n)) = _
  rw [realQuadratureMap_rotate, realQuadratureRotate_eq_rotateRealPlane]
  rfl

theorem materialLogPhase_planeEnergy {N : ℕ} (t : ℝ) (X : MaterialVerticalCarrier N)
    (n : Fin N) (k : ℕ) :
    realPlaneEnergy (materialVerticalPlaneAt (materialLogPhase t X) n k) =
      realPlaneEnergy (materialVerticalPlaneAt X n k) := by
  rw [materialLogPhase_planeAt]
  exact materialLogRotate_energy _ _ _

theorem materialLogPhase_finiteEnergy {N : ℕ} (t : ℝ)
    (X : MaterialVerticalCarrier N) (K : ℕ) :
    (∑ n : Fin N, ∑ k ∈ Finset.range K,
      realPlaneEnergy (materialVerticalPlaneAt (materialLogPhase t X) n k)) =
    ∑ n : Fin N, ∑ k ∈ Finset.range K, realPlaneEnergy (materialVerticalPlaneAt X n k) := by
  simp_rw [materialLogPhase_planeEnergy]

/-- Reuse the existing center-leg readout at an evaluated coordinate. This is
not a new global Defect, nor an identification of camera radius with depth. -/
theorem materialLogPhase_centerLeg_orbit {N : ℕ} (q t : ℝ)
    (X : MaterialVerticalCarrier N) (n : Fin N) (k : ℕ) :
    centerLegForm q 0 (materialVerticalPlaneAt (materialLogPhase t X) n k) =
      materialLogRotate t n.val (centerLegForm q 0 (materialVerticalPlaneAt X n k)) := by
  rw [materialLogPhase_planeAt]
  have h : centerLegForm q 0 (materialLogRotate t n.val (materialVerticalPlaneAt X n k)) =
      centerLegForm q (materialLogAngle t n.val) (materialVerticalPlaneAt X n k) := by
    rw [centerLegForm_eq_closed, centerLegForm_eq_closed, rotateRealPlane_zero]
    rfl
  rw [h, centerLegForm_eq_rotate_zero]
  rfl

theorem materialLogPhase_centerLeg_zero_iff {N : ℕ} (q t : ℝ)
    (X : MaterialVerticalCarrier N) (n : Fin N) (k : ℕ) :
    centerLegForm q 0 (materialVerticalPlaneAt (materialLogPhase t X) n k) = (0, 0) ↔
      centerLegForm q 0 (materialVerticalPlaneAt X n k) = (0, 0) := by
  rw [materialLogPhase_centerLeg_orbit]
  exact materialLogRotate_eq_zero_iff _ _ _

theorem materialTfvdSynthesized_centerLeg_zero_iff {N : ℕ} (eta : ℝ)
    (h0 : 0 < eta) (h1 : eta < 1) (q t : ℝ) (X : MaterialVerticalCarrier N)
    (n : Fin N) (k : ℕ) :
    centerLegForm q 0 (materialVerticalPlaneAt
      (materialTfvdSynthesis eta h0.le h1
        (materialLogPhase t (materialTfvdAnalysis eta X))) n k) = (0, 0) ↔
      centerLegForm q 0 (materialVerticalPlaneAt X n k) = (0, 0) := by
  rw [materialTfvdSynthesized_logOrbit eta h0 h1]
  exact materialLogPhase_centerLeg_zero_iff _ _ _ _ _

end

end GeometryOfNumbers.Analysis
