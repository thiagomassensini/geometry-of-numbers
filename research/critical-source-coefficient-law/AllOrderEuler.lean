import EulerOrientation

/-! Exact Euler/nonlinear split in arbitrary original jet dimension. It
separates a source contribution, not a new metric or a substitute Gram. -/
namespace CarrySourceLaw
open CarrySelfAdjointOperator CarrySelfAdjointOperator.ChiralReturn
open CarryCriticalMixed CarryCriticalRelative Filter Topology
open scoped BigOperators ComplexConjugate InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem forwardWeight_sum (M a : ℕ) (ha : a < M) :
    (∑ r : Fin M, completedGreenForwardWeight a r.val) = if a=0 then 1 else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun r : ℕ => completedGreenForwardWeight a r) M]
  have he : (∑ r ∈ Finset.range M, completedGreenForwardWeight a r) =
      ∑ r ∈ Finset.range (a+1), completedGreenForwardWeight a r := by
    symm
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro r _ hr
    have hlt : a < r := by
      have hn : ¬ r < a+1 := by simpa only [Finset.mem_range] using hr
      omega
    simp [completedGreenForwardWeight, Nat.choose_eq_zero_of_lt hlt]
  rw [he]
  by_cases hz : a=0
  · subst a; norm_num [completedGreenForwardWeight]
  · have hh := completedGreenForwardWeightPower_eq_zero_of_lt (order := a) (degree := 0)
      (by omega)
    simpa [completedGreenForwardWeightPower, hz] using hh

/-- All higher finite differences cancel in the zeroth endpoint readout.
Their physical vectors have NOT been discarded. -/
theorem stencil_sum (n k : ℕ) (hn : 0 < 2*n) (x : Fin (2*n) → ℂ) :
    (∑ r, jetStencil n k x r) = x ⟨0,hn⟩ := by
  classical
  unfold jetStencil
  rw [Finset.sum_comm]
  have he (a : Fin (2*n)) :
      (∑ r : Fin (2*n), nativeSourceJetOrderPhase a *
        (((a.val.factorial:ℂ)*CarryCriticalRelative.step k^a.val)⁻¹) *
          completedGreenForwardWeight a r * x a) =
      nativeSourceJetOrderPhase a *
        (((a.val.factorial:ℂ)*CarryCriticalRelative.step k^a.val)⁻¹) * x a *
          (∑ r : Fin (2*n), completedGreenForwardWeight a r) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    ring
  simp_rw [he, forwardWeight_sum (2*n) _ (Fin.isLt _)]
  rw [Finset.sum_eq_single (⟨0,hn⟩ : Fin (2*n))]
  · simp [nativeSourceJetOrderPhase]
  · intro a _ hne
    have hv : a.val ≠ 0 := by intro ha; exact hne (Fin.ext ha)
    simp [hv]
  · simp

def nonlinearReadout (n k : ℕ) (x : Fin (2*n) → ℂ) : ℝ :=
  let d := radialCompletedValueCoefficients k (nativeSourceChiralJetInput n k x)
  4*(inner ℂ (radialIncidentSynthesis k (2*n) d)
    (radialCompletedRemainderSynthesis k (2*n) d)).re

/-- Exact original-source split: only x0 appears in the first Euler term;
all other physical coordinates and all crosses stay in the nonlinear term. -/
theorem all_order_euler_exact (n k : ℕ) (hn : 0 < 2*n) (x : Fin (2*n) → ℂ)
    (hF : ∀ r : Fin (2*n), completedNativeOperatorCharacteristic
      (canonicalCompletedC3RadialTiltPoint k r) ≠ 0)
    (hP : ∀ r : Fin (2*n), completedNativePositiveHermiteBiehlerCoordinate
      (canonicalCompletedC3RadialTiltPoint k r) ≠ 0) :
    (storage k (nativeSourceChiralJetInput n k x) 1).re =
      2*canonicalCompletedNativeLogDerivativeMoment 0*Complex.normSq (x ⟨0,hn⟩) +
        nonlinearReadout n k x := by
  have hsum : (∑ r : Fin (2*n), radialCompletedValueCoefficients k
      (nativeSourceChiralJetInput n k x) r) = (Real.sqrt 2:ℂ)⁻¹*x ⟨0,hn⟩ := by
    rw [valueCoefficients_eq_stencil n k x hF hP]
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, stencil_sum n k hn]
  rw [storage_one_eq_euler_boundary_add_remainder k (2*n) _ hF hP,
    hsum, eulerScale_eq_sourceCoefficient]
  have hs : Complex.normSq ((Real.sqrt 2:ℂ)⁻¹) = (1:ℝ)/2 := by
    rw [Complex.normSq_inv, Complex.normSq_ofReal, ← pow_two, Real.sq_sqrt (by norm_num)]
    norm_num
  rw [Complex.normSq_mul, hs, sourceCoefficient_eq_canonical]
  change 2*((k:ℝ)+1)*(2*canonicalCompletedNativeLogDerivativeMoment 0/((k:ℝ)+1))*
      (1/2*Complex.normSq (x ⟨0,hn⟩)) + nonlinearReadout n k x = _
  have hk : (k:ℝ)+1 ≠ 0 := by positivity
  field_simp

/-- Source-only limit in every finite jet dimension. This identifies the
nonlinear coefficient but does NOT assign it a sign. -/
theorem all_order_nonlinear_tendsto (n : ℕ) (hn : 0 < 2*n) (x : Fin (2*n) → ℂ) :
    Tendsto (fun k => nonlinearReadout n k x) atTop
      (nhds (nativeSourceFiniteBoundaryEnergy (2*n) x / 2 -
        2*canonicalCompletedNativeLogDerivativeMoment 0*Complex.normSq (x ⟨0,hn⟩))) := by
  have ht := (nativeSourceProjectiveBoundaryJetSynthesis_energy_tendsto n x).div_const 2
  have hs : Tendsto (fun k => (storage k (nativeSourceChiralJetInput n k x) 1).re)
      atTop (nhds (nativeSourceFiniteBoundaryEnergy (2*n) x/2)) := by
    simpa only [nativeSourceProjectiveBoundaryJetSynthesis_energy_eq_storage,
      mul_div_cancel_left₀ _ (by norm_num : (2:ℝ) ≠ 0)] using ht
  have hh := hs.sub_const
    (2*canonicalCompletedNativeLogDerivativeMoment 0*Complex.normSq (x ⟨0,hn⟩))
  apply hh.congr'
  filter_upwards [canonicalCompletedNativeRadialProjectiveChiral_eventually_regular (2*n)]
    with k hk
  rw [all_order_euler_exact n k hn x (fun r => (hk r).2.1) (fun r => (hk r).2.2)]
  ring

/-- The finite critical residual after removing Euler is exactly sigma minus
its zeroth-coordinate budget. Only old-prefix invertibility is used. -/
theorem critical_nonlinear_tendsto (s : Fin 2) (n : ℕ)
    (hA : IsUnit (sourceMomentMatrix CarryCriticalSource.h s.val n)) :
    Tendsto (fun k => nonlinearReadout (n+1) k (CarryCriticalSource.criticalCoordinates s n))
      atTop (nhds (2*sourceMomentSchur CarryCriticalSource.h s.val n -
        2*canonicalCompletedNativeLogDerivativeMoment 0 * Complex.normSq
          (CarryCriticalSource.criticalCoordinates s n ⟨0,by omega⟩))) := by
  have ht := all_order_nonlinear_tendsto (n+1) (by omega)
    (CarryCriticalSource.criticalCoordinates s n)
  rw [critical_boundary_of_isUnit s n hA] at ht
  have he : 4*sourceMomentSchur CarryCriticalSource.h s.val n/2 =
      2*sourceMomentSchur CarryCriticalSource.h s.val n := by ring
  rw [he] at ht
  exact ht

/-- The odd critical sector has no zeroth even coordinate; this is exact
parity bookkeeping, not a compression of its physical state. -/
theorem critical_odd_zero_coordinate (n : ℕ) :
    CarryCriticalSource.criticalCoordinates 1 n ⟨0,by omega⟩ = 0 := by
  simp [CarryCriticalSource.criticalCoordinates, CarryCriticalSource.parityCoordinates,
    nativeSourceBoundaryFromParity]

/-- On every odd critical direction the original nonlinear readout is the
WHOLE balance. Its sign therefore cannot be supplied as a new independent
all-order hypothesis for that same balance. -/
theorem critical_odd_nonlinear_exact (n k : ℕ)
    (hF : ∀ r : Fin (2*(n+1)), completedNativeOperatorCharacteristic
      (canonicalCompletedC3RadialTiltPoint k r) ≠ 0)
    (hP : ∀ r : Fin (2*(n+1)), completedNativePositiveHermiteBiehlerCoordinate
      (canonicalCompletedC3RadialTiltPoint k r) ≠ 0) :
    nonlinearReadout (n+1) k (CarryCriticalSource.criticalCoordinates 1 n) =
      CarryCriticalSource.criticalBalance 1 n k := by
  rw [CarryCriticalSource.criticalBalance_eq_storage]
  simp only [CarryCriticalSource.criticalInput]
  rw [all_order_euler_exact (n+1) k (by omega) _ hF hP, critical_odd_zero_coordinate]
  simp

theorem critical_odd_nonlinear_tendsto (n : ℕ)
    (hA : IsUnit (sourceMomentMatrix CarryCriticalSource.h 1 n)) :
    Tendsto (fun k => nonlinearReadout (n+1) k (CarryCriticalSource.criticalCoordinates 1 n))
      atTop (nhds (2*sourceMomentSchur CarryCriticalSource.h 1 n)) := by
  have ht := critical_nonlinear_tendsto 1 n hA
  simpa only [Fin.val_one, critical_odd_zero_coordinate, Complex.normSq_zero,
    mul_zero, sub_zero] using ht

end
end CarrySourceLaw
