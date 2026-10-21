import ResidualEuler
import EvenTrialData

/-! Independent finite sign test from immutable PR34 source enclosures.
We import the boxes and the original rational trial polynomial, NOT the
seventh positivity certificate. This direction is close to, but is not
asserted equal to, the exact monic PR41 residual. -/
namespace CarryResidualEuler
open CarrySelfAdjointOperator ChiralReturn CarryJetOverlap CarryFiberTransport
open NativeMomentOrthogonalization GeometryOfNumbers.Analysis
open CarryIntegralCertificate CarrySeventhEven CarryCriticalSource
open scoped BigOperators InnerProductSpace ComplexConjugate
open Filter Topology
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 48000000

/-- The literal pre-existing column six of PR34, with its original scale. -/
def seventhTrialBoundary : Fin 14 → ℂ :=
  nativeSourceBoundaryFromParity 7 (fun i => ((trialCoefficient i.val 6 : ℝ) : ℂ)) 0

/-- Its complete source quadratic form, with every ordered cross term. -/
theorem seventh_trial_energy :
    nativeSourceFiniteBoundaryEnergy 14 seventhTrialBoundary = 4*trialPairing 6 6 := by
  change nativeSourceFiniteBoundaryEnergy (2*7)
    (nativeSourceBoundaryFromParity 7 (fun i => ((trialCoefficient i.val 6:ℝ):ℂ)) 0) = _
  rw [native_boundary_real_even, momentForm_coefficients]
  congr 1
  unfold carryPairingBilinear trialPairing
  rw [← Fin.sum_univ_eq_sum_range (fun a => ∑ b ∈ Finset.range 7,
    (trialCoefficient a 6:ℝ)*h (a+b)*(trialCoefficient b 6:ℝ)) 7]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Fin.sum_univ_eq_sum_range (fun b =>
    (trialCoefficient a.val 6:ℝ)*h (a.val+b)*(trialCoefficient b 6:ℝ)) 7]
  apply Finset.sum_congr rfl
  intro b _
  dsimp only
  ring

theorem seventh_trial_zero :
    Complex.normSq (seventhTrialBoundary 0) = (trialCoefficient 0 6 : ℝ)^2 := by
  simp [seventhTrialBoundary, nativeSourceBoundaryFromParity, pow_two]

/-- No finite sign certificate is consumed to certify this pairing box. -/
theorem trial_pairing_mem (i j : ℕ) : (trialPairingBox i j).Mem (trialPairing i j) := by
  have hm : (rawTrialPairingBox i j).Mem (trialPairing i j) :=
    mem_sum _ _ 7 (fun a _ => mem_sum _ _ 7 (fun b _ =>
      mem_mul (mem_mul (mem_ofRat _) (mem_compactMomentBox (a+b))) (mem_ofRat _)))
  by_cases hi : i < 7
  · by_cases hj : j < 7
    · exact mem_of_contained hm (trial_pairing_checks ⟨i,hi⟩ ⟨j,hj⟩)
    · simp only [trialPairingBox, dif_pos hi, dif_neg hj, Box.Mem]
  · simp only [trialPairingBox, dif_neg hi, Box.Mem]

/-- Half of the limiting nonlinear contribution in this SAME direction. -/
def seventhNonlinearMargin : ℝ :=
  trialPairing 6 6-h 0*(trialCoefficient 0 6:ℝ)^2

def seventhNonlinearBox : Box :=
  (trialPairingBox 6 6).add
    ((compactMomentBox 0).mul (Box.ofRat ((trialCoefficient 0 6)^2))).neg

theorem seventh_nonlinear_mem : seventhNonlinearBox.Mem seventhNonlinearMargin := by
  have hm := mem_add (trial_pairing_mem 6 6)
    (mem_neg (mem_mul (mem_compactMomentBox 0) (mem_ofRat ((trialCoefficient 0 6)^2))))
  simpa only [seventhNonlinearBox, seventhNonlinearMargin, Rat.cast_pow, sub_eq_add_neg] using hm

/-- Rational interval comparisons checked by Lean's kernel. -/
theorem seventh_nonlinear_checks :
    ((seventhNonlinearBox).add (Box.rat 2 5)).positive = true ∧
    ((Box.rat (-1) 5).add seventhNonlinearBox.neg).positive = true ∧
    ((trialPairingBox 6 6).add (Box.point 5).neg).positive = true := by
  decide +kernel

/-- The full nonlinear companion has a STRICTLY NEGATIVE finite part in
an actual native-source direction. This does not assert a negative pivot. -/
theorem seventh_nonlinear_bounds :
    -(2/5:ℝ) < seventhNonlinearMargin ∧ seventhNonlinearMargin < -(1/5:ℝ) := by
  have hl := pos_of_mem (mem_add seventh_nonlinear_mem (mem_rat 2 5))
    seventh_nonlinear_checks.1
  have hu := pos_of_mem (mem_add (mem_rat (-1) 5) (mem_neg seventh_nonlinear_mem))
    seventh_nonlinear_checks.2.1
  norm_num only [Int.cast_ofNat, Int.cast_neg, Int.cast_one] at hl hu
  constructor <;> linarith only [hl,hu]

/-- Independent positive total source margin coexists with the negative
nonlinear term; no seventh-pivot positivity theorem is imported. -/
theorem seventh_trial_positive_margin : 5 < trialPairing 6 6 := by
  have hp := pos_of_mem (mem_add (trial_pairing_mem 6 6) (mem_neg (mem_point 5)))
    seventh_nonlinear_checks.2.2
  norm_num only [Int.cast_ofNat] at hp
  linarith only [hp]

theorem seventh_nonlinear_tendsto :
    Tendsto (fun k => nonlinearReadout 7 k seventhTrialBoundary) atTop
      (nhds (2*seventhNonlinearMargin)) := by
  have ht := nonlinear_tendsto 6 seventhTrialBoundary
  rw [seventh_trial_energy, seventh_trial_zero] at ht
  have he : 4*trialPairing 6 6/2-2*h 0*(trialCoefficient 0 6:ℝ)^2 =
      2*seventhNonlinearMargin := by unfold seventhNonlinearMargin; ring
  rw [he] at ht
  exact ht

theorem seventh_nonlinear_eventually_negative :
    ∀ᶠ k : ℕ in atTop, nonlinearReadout 7 k seventhTrialBoundary < 0 := by
  exact (tendsto_order.mp seventh_nonlinear_tendsto).2 0
    (by linarith [seventh_nonlinear_bounds.2])

/-- Concrete instance of the PR48 requested RELATIVE subtraction bound,
from the source boxes and exact Euler transport, allowing a negative N. -/
theorem seventh_trial_relative_budget :
    ∀ᶠ k : ℕ in atTop, ∀ hs : strip k 14,
      5 < (dampedCameraBalance k (nativeSourceChiralJetInput 7 k seventhTrialBoundary)
        (nativeSourceChiralJetInput 7 k seventhTrialBoundary) hs).re+
      (variableDefect k (nativeSourceChiralJetInput 7 k seventhTrialBoundary)
        (nativeSourceChiralJetInput 7 k seventhTrialBoundary) hs).re := by
  have ht := (seventh_nonlinear_tendsto.div_const 2).const_add
    (h 0*(trialCoefficient 0 6:ℝ)^2)
  have he : h 0*(trialCoefficient 0 6:ℝ)^2+2*seventhNonlinearMargin/2 = trialPairing 6 6 := by
    unfold seventhNonlinearMargin
    ring
  rw [he] at ht
  have hevent := (tendsto_order.mp ht).1 5 seventh_trial_positive_margin
  filter_upwards [hevent,canonicalCompletedNativeRadialProjectiveChiral_eventually_regular 14]
    with k hk hreg
  intro hs
  rw [← Complex.add_re, ← jetBudget_eq_damped_add_defect]
  rw [budget_euler_exact 6 k seventhTrialBoundary hs
    (fun r => (hreg r).2.1) (fun r => (hreg r).2.2), seventh_trial_zero]
  exact hk

/-- Same eventual physical source: negative nonlinear contribution AND
strictly positive full budget. Neither condition erases the other. -/
theorem seventh_signed_compensation :
    ∀ᶠ k : ℕ in atTop, ∀ hs : strip k 14,
      nonlinearReadout 7 k seventhTrialBoundary < 0 ∧
      5 < (dampedCameraBalance k (nativeSourceChiralJetInput 7 k seventhTrialBoundary)
        (nativeSourceChiralJetInput 7 k seventhTrialBoundary) hs).re+
      (variableDefect k (nativeSourceChiralJetInput 7 k seventhTrialBoundary)
        (nativeSourceChiralJetInput 7 k seventhTrialBoundary) hs).re := by
  filter_upwards [seventh_nonlinear_eventually_negative,seventh_trial_relative_budget]
    with k hn hb
  intro hs
  exact ⟨hn,hb hs⟩


end
end CarryResidualEuler
