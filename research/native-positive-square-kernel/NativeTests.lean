import SquareEnergy
import ShiftMoments
import SourceSquare
import CarrySelfAdjointOperator.C2GlobalGreenBridge
import OddSourceBoxes

namespace CarryPositiveSquare
open CarrySelfAdjointOperator CarrySelfAdjointOperator.C2GlobalGreenBridge
open GeometryOfNumbers.Analysis CarrySixthOdd CarryIntegralCertificate NativeMomentOrthogonalization
open Filter Topology
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000

/-- Reuse the original low-order source boxes (the comparison already used
in PR36), rather than derive a candidate's spectrum from desired heights. -/
theorem native_low_order_comparison :
    0 < canonicalCompletedNativeLogDerivativeMoment 1 ∧
    canonicalCompletedNativeLogDerivativeMoment 2 < canonicalCompletedNativeLogDerivativeMoment 1/16 := by
  have h1 := mem_compactMomentBox 1
  have h2 := mem_compactMomentBox 2
  norm_num [compactMomentBox,compactMomentTable,Box.Mem,intervalScale] at h1 h2
  constructor <;> linarith

/-- The actual original Green B*B exists and is positive, but its lower frame
bound contradicts the REQUIRED first column for EVERY source v. This tests
this Gram operator, not the completed return-defect realization. -/
theorem original_green_square_not_canonical (t : ℝ) (v : CoreState) :
    ¬ (∀ n : ℕ, canonicalCompletedNativeLogDerivativeMoment n =
      weightedMoment (c2GlobalRestrictedGreenGram t) v n) := by
  intro h
  have hb := weighted_moment_gap (c2GlobalGreenAnalysis t) v (1/2)
    (fun x => (c2GlobalGreenAnalysis_norm_sq_bounds t x).1)
  change (1/2:ℝ)*weightedMoment (c2GlobalRestrictedGreenGram t) v 1 ≤
    weightedMoment (c2GlobalRestrictedGreenGram t) v 2 at hb
  rw [← h 1,← h 2] at hb
  linarith [native_low_order_comparison.1,native_low_order_comparison.2]

/-- The positive square of the full one-point return defect loses the
nonzero canonical central coefficient on the SAME original source. -/
theorem squared_defect_not_canonical_mass :
    ¬ Tendsto (fun k => ‖ChiralReturn.radialReturnEnergyDefect k 1 (oneSource k)‖^2/2)
      atTop (nhds (canonicalCompletedNativeLogDerivativeMoment 0)) := by
  intro ht
  have hz := one_squared_energy_tendsto_zero.div_const 2
  norm_num only [zero_div] at hz
  have he := tendsto_nhds_unique hz ht
  exact (ne_of_gt canonicalCompletedNativeLogDerivativeMoment_zero_pos) he.symm

/-- A genuine finite source test: its H3 form is strict, so no exact
second-order scalar recurrence can hold for the canonical sequence. -/
theorem native_no_order_two_recurrence (a b : ℝ) :
    ¬ (∀ n : ℕ, canonicalCompletedNativeLogDerivativeMoment (n+2) =
      a*canonicalCompletedNativeLogDerivativeMoment (n+1)+b*canonicalCompletedNativeLogDerivativeMoment n) := by
  intro hr
  let q : Fin 3 → ℝ := ![-b,-a,1]
  let x := nativeSourceBoundaryFromParity 3 (fun i => (q i:ℂ)) 0
  have hx : x ≠ 0 := by
    intro hh
    have hz := congrFun hh (4:Fin 6)
    norm_num [x,q,nativeSourceBoundaryFromParity] at hz
  have hp := nativeSourceSixBoundaryEnergy_pos x hx
  rw [← nativeSourceFiniteBoundaryEnergy_six] at hp
  change 0 < nativeSourceFiniteBoundaryEnergy (2*3)
    (nativeSourceBoundaryFromParity 3 (fun i => (q i:ℂ)) 0) at hp
  rw [native_boundary_real_even, momentForm_coefficients] at hp
  have hrow (i : Fin 3) :
      (∑ j : Fin 3, canonicalCompletedNativeLogDerivativeMoment (i.val+j.val)*q j)=0 := by
    simp only [q,Fin.sum_univ_succ,Fin.sum_univ_zero,Matrix.cons_val_zero,Matrix.cons_val_succ,
      Fin.val_zero,Fin.val_succ,mul_one,add_zero]
    have hh := hr i.val
    linear_combination hh
  have hz : carryPairingBilinear
      (fun i j => canonicalCompletedNativeLogDerivativeMoment (i+j)) 3 q q = 0 := by
    unfold carryPairingBilinear
    have he (i : Fin 3) :
        (∑ j : Fin 3, canonicalCompletedNativeLogDerivativeMoment (i+j)*q i*q j) =
          q i*(∑ j : Fin 3, canonicalCompletedNativeLogDerivativeMoment (i+j)*q j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    simp_rw [he,hrow,mul_zero]
    simp
  rw [hz] at hp
  norm_num at hp

/-- The squared ORIGINAL physical Cauchy--Laguerre shift cannot supply the
canonical first column, for ANY source, even if its mass were calibrated. -/
theorem physical_shift_square_not_canonical (v : CarrySelfAdjointOperator.NativeLaguerre.PhysicalCauchySpace) :
    ¬ (∀ n : ℕ, canonicalCompletedNativeLogDerivativeMoment n = shiftWeightedMoment v n) := by
  intro hh
  apply native_no_order_two_recurrence (2-‖boundaryVector‖^2) (-(1-‖boundaryVector‖^2))
  intro n
  rw [hh (n+2),hh (n+1),hh n,shift_moment_recurrence]
  ring


end
end CarryPositiveSquare
