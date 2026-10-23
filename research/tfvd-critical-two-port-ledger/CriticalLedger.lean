import FixedSourceTfvd

namespace CarryTfvdCritical
open CarrySelfAdjointOperator PhysicalSewing NativeLaguerre ChiralReturn CarryCriticalSource
open Filter Topology
open scoped BigOperators Matrix ComplexConjugate InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

/-- Convert only after the complete two-leg jet synthesis. -/
theorem jet_form_re_eq_excess (n k : ℕ) (x : Fin (2*n) → ℂ) :
    (canonicalCompletedNativeProjectiveChiralForm
      (nativeSourceProjectiveBoundaryJetSynthesis n k x)
      (nativeSourceProjectiveBoundaryJetSynthesis n k x)).re =
        CarryNegativeDirection.returnExcess n k x / (-2) := by
  unfold canonicalCompletedNativeProjectiveChiralForm CarryNegativeDirection.returnExcess
  simp only [inner_self_eq_norm_sq_to_K]
  norm_num [Complex.mul_re, Complex.sub_re, div_eq_mul_inv, ← Complex.ofReal_pow]
  ring

/-- Uniform in the exact TFVD cutoff; the head may depend on it, but the total does not. -/
theorem original_flux_ledger_eventually (n : ℕ) :
    ∀ᶠ k : ℕ in atTop, ∀ M : ℕ, ∀ x : Fin (2*n) → ℂ,
      headFlux M n k x + correctionFlux M n k x = CarryNegativeDirection.returnExcess n k x / (-2) := by
  filter_upwards [fullSource_eventually_eq_original n] with k hk M x
  rw [← full_head_real_ledger, hk M x, jet_form_re_eq_excess]

/-- Exact tails allow an arbitrary moving TFVD cutoff without exchanging analytic limits. -/
theorem total_flux_tendsto (n : ℕ) (x : Fin (2*n) → ℂ) (cutoff : ℕ → ℕ) :
    Tendsto (fun k => headFlux (cutoff k) n k x + correctionFlux (cutoff k) n k x)
      atTop (nhds (nativeSourceFiniteBoundaryEnergy (2*n) x / 4)) := by
  have ht := (CarryNegativeDirection.returnExcess_tendsto n x).div_const (-2)
  have hc : (-nativeSourceFiniteBoundaryEnergy (2*n) x/2)/(-2) =
      nativeSourceFiniteBoundaryEnergy (2*n) x/4 := by ring
  rw [hc] at ht
  apply ht.congr'
  filter_upwards [original_flux_ledger_eventually n] with k hk
  exact (hk (cutoff k) x).symm

/-- The SAME critical coordinate selected in PR41/64, with only invertibility of the old prefix. -/
theorem critical_total_flux_tendsto (s : Fin 2) (n : ℕ)
    (hA : IsUnit (sourceMomentMatrix h s.val n)) (cutoff : ℕ → ℕ) :
    Tendsto (fun k => headFlux (cutoff k) (n+1) k (criticalCoordinates s n) +
      correctionFlux (cutoff k) (n+1) k (criticalCoordinates s n)) atTop
      (nhds (sourceMomentSchur h s.val n)) := by
  have he := NativeMomentOrthogonalization.native_inverseSchur_boundary_energy s n hA
  have hh : nativeSourceFiniteBoundaryEnergy (2*(n+1)) (criticalCoordinates s n) =
      4*sourceMomentSchur h s.val n := by
    fin_cases s <;> simpa [criticalCoordinates,parityCoordinates,criticalCoefficients,h] using he
  have ht := total_flux_tendsto (n+1) (criticalCoordinates s n) cutoff
  rw [hh] at ht
  simpa using ht

/-- This is a bound in the OLD physical metric; no Euclidean jet norm is substituted. -/
theorem correctionFlux_abs_bound (M n k : ℕ) (x : Fin (2*n) → ℂ) :
    |correctionFlux M n k x| ≤
      ‖radialIncidentSynthesis k (2*n) (fixedMaterial n k x)‖ *
      ‖radialIncidentSynthesis k (2*n) (errorSecond M n k x)‖ := by
  have he : correctionFlux M n k x =
      (inner ℂ (radialIncidentSynthesis k (2*n) (fixedMaterial n k x))
        (radialIncidentSynthesis k (2*n) (errorSecond M n k x))).im := by
    rw [incident_inner_eq_matrixPairing]
    simp [correctionFlux,portFlux,Complex.mul_im]
  rw [he]
  exact (Complex.abs_im_le_norm _).trans (norm_inner_le_norm _ _)

end
end CarryTfvdCritical
