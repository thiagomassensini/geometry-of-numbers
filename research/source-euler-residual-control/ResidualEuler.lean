import PR41Bridge
import CarrySelfAdjointOperator.CompletedNativeChiralReturnEulerBoundary
import CarrySelfAdjointOperator.CompletedNativeCentralChiralQuotientCurvature

/-! Euler extraction of the SAME full source in the PR41 directions.
The nonlinear readout remains a mixed pairing in the original Cauchy space.
No theta sign, source contractivity or next-pivot positivity is assumed. -/
namespace CarryResidualEuler
open CarrySelfAdjointOperator ChiralReturn CarryJetOverlap CarryFiberTransport
open NativeMomentOrthogonalization GeometryOfNumbers.Analysis
open scoped BigOperators InnerProductSpace ComplexConjugate
open Filter Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- Original value amplitudes, after the already proved jet-input map. -/
def jetValues (n k : ℕ) (x : Fin (2*n) → ℂ) : Fin (2*n) → ℂ :=
  radialCompletedValueCoefficients k (nativeSourceChiralJetInput n k x)

/-- The complete nonlinear companion; no Taylor term is discarded. -/
def nonlinearReadout (n k : ℕ) (x : Fin (2*n) → ℂ) : ℝ :=
  4*(inner ℂ (radialIncidentSynthesis k (2*n) (jetValues n k x))
    (radialCompletedRemainderSynthesis k (2*n) (jetValues n k x))).re

/-- Forward differences annihilate the constant before any quadratic readout. -/
theorem forward_weights_sum (M a : ℕ) (ha : a < M) :
    (∑ r : Fin M, completedGreenForwardWeight a r.val) = if a=0 then 1 else 0 := by
  have he : (∑ r : Fin M, completedGreenForwardWeight a r.val) =
      completedGreenForwardWeightPower a 0 := by
    rw [Fin.sum_univ_eq_sum_range (fun r => completedGreenForwardWeight a r) M]
    unfold completedGreenForwardWeightPower
    simp only [pow_zero, mul_one]
    symm
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro r _ hr
    have hlt : a < r := by
      have hh : ¬r < a+1 := by simpa only [Finset.mem_range] using hr
      omega
    simp [completedGreenForwardWeight, Nat.choose_eq_zero_of_lt hlt]
  rw [he]
  split_ifs with hz
  · subst a
    norm_num [completedGreenForwardWeightPower, completedGreenForwardWeight]
  · exact completedGreenForwardWeightPower_eq_zero_of_lt (by omega)

/-- Cancel only the original F and E+ factors in each value coefficient. -/
theorem jet_value_eq_sum (n k : ℕ) (x : Fin (2*n) → ℂ)
    (hF : ∀ r : Fin (2*n), completedNativeOperatorCharacteristic (radialPoint k r) ≠ 0)
    (hP : ∀ r : Fin (2*n), completedNativePositiveHermiteBiehlerCoordinate (radialPoint k r) ≠ 0)
    (r : Fin (2*n)) :
    jetValues n k x r = (Real.sqrt 2 : ℂ)⁻¹ *
      ∑ a : Fin (2*n), nativeSourceJetOrderPhase a *
        (((a.val.factorial : ℂ)*canonicalCompletedC3RadialSecondStep k^a.val)⁻¹)*
          completedGreenForwardWeight a r*x a := by
  unfold jetValues radialCompletedValueCoefficients nativeSourceChiralJetInput
  simp only [LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_mul, Finset.sum_div,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  unfold nativeSourceChiralJetInputMatrix completedNativeNormalizedPositiveChiralAmplitude
    canonicalCompletedC3FullWronskianChiralNormalization
  field_simp [hF r, hP r]

/-- Only the zeroth boundary coefficient survives the exact Euler sum. -/
theorem jet_values_sum (n k : ℕ) (x : Fin (2*(n+1)) → ℂ)
    (hF : ∀ r : Fin (2*(n+1)), completedNativeOperatorCharacteristic (radialPoint k r) ≠ 0)
    (hP : ∀ r : Fin (2*(n+1)), completedNativePositiveHermiteBiehlerCoordinate (radialPoint k r) ≠ 0) :
    (∑ r, jetValues (n+1) k x r) = (Real.sqrt 2 : ℂ)⁻¹*x 0 := by
  simp_rw [jet_value_eq_sum (n+1) k x hF hP]
  rw [← Finset.mul_sum, Finset.sum_comm]
  have he (a : Fin (2*(n+1))) :
      (∑ r : Fin (2*(n+1)), nativeSourceJetOrderPhase a *
        (((a.val.factorial : ℂ)*canonicalCompletedC3RadialSecondStep k^a.val)⁻¹)*
          completedGreenForwardWeight a r*x a) = if a=0 then x 0 else 0 := by
    rw [← Finset.sum_mul, ← Finset.mul_sum, forward_weights_sum _ _ a.isLt]
    by_cases ha : a=0
    · subst a
      simp [nativeSourceJetOrderPhase]
    · have hn : a.val ≠ 0 := fun hh => ha (Fin.ext hh)
      simp [ha, hn]
  simp_rw [he]
  simp

/-- The degree scale comes from the completed characteristic curvature,
without using positivity of the canonical sequence. -/
theorem euler_scale_native (k : ℕ) :
    radialCompletedEulerScale k = 2*canonicalCompletedNativeLogDerivativeMoment 0/((k:ℝ)+1) := by
  have hm := canonicalCompletedNativeLogDerivativeMoment_zero_eq_characteristicCurvature_chiral
  have he : -iteratedDeriv 2 completedNativeOperatorCharacteristic 0 /
      completedNativeOperatorCharacteristic 0 =
        2*(canonicalCompletedNativeLogDerivativeMoment 0:ℂ) := by
    rw [hm]
    ring
  unfold radialCompletedEulerScale
  rw [he]
  simp

/-- All orders and both real quadratures: a positive rank-one contribution
plus the untouched nonlinear mixed source pairing. -/
theorem storage_jet_euler_exact (n k : ℕ) (x : Fin (2*(n+1)) → ℂ)
    (hF : ∀ r : Fin (2*(n+1)), completedNativeOperatorCharacteristic (radialPoint k r) ≠ 0)
    (hP : ∀ r : Fin (2*(n+1)), completedNativePositiveHermiteBiehlerCoordinate (radialPoint k r) ≠ 0) :
    (storage k (nativeSourceChiralJetInput (n+1) k x) 1).re =
      2*canonicalCompletedNativeLogDerivativeMoment 0*Complex.normSq (x 0)+nonlinearReadout (n+1) k x := by
  rw [storage_one_eq_euler_boundary_add_remainder k (2*(n+1)) _ hF hP]
  change _ + nonlinearReadout (n+1) k x = _
  rw [← jetValues, jet_values_sum n k x hF hP, euler_scale_native]
  have hs : Complex.normSq ((Real.sqrt 2:ℂ)⁻¹) = (1:ℝ)/2 := by
    rw [Complex.normSq_inv, Complex.normSq_ofReal, ← pow_two, Real.sq_sqrt (by norm_num)]
    norm_num
  rw [Complex.normSq_mul, hs]
  have hk : (k:ℝ)+1 ≠ 0 := by positivity
  field_simp

/-- New exact identification of the PR48 relative subtraction problem with
an Euler term and the complete nonlinear source remainder. -/
theorem budget_euler_exact (n k : ℕ) (x : Fin (2*(n+1)) → ℂ)
    (hs : strip k (2*(n+1)))
    (hF : ∀ r : Fin (2*(n+1)), completedNativeOperatorCharacteristic (radialPoint k r) ≠ 0)
    (hP : ∀ r : Fin (2*(n+1)), completedNativePositiveHermiteBiehlerCoordinate (radialPoint k r) ≠ 0) :
    (jetBudget (n+1) k x x hs).re =
      canonicalCompletedNativeLogDerivativeMoment 0*Complex.normSq (x 0)+nonlinearReadout (n+1) k x/2 := by
  have h := congrArg Complex.re (jet_pairing_source_balance (n+1) k x x hP)
  rw [polarizedSourceBalance_self_eq_storage k _ 1 hP] at h
  have hb := jetBudget_eq_original_pairing (n+1) k x x hs hP
  rw [← hb] at h
  norm_num [Complex.mul_re, Complex.mul_im] at h
  rw [storage_jet_euler_exact n k x hF hP] at h
  linarith

/-- Quantitative nonlinear finite part for EVERY fixed original boundary.
No sign or matrix inverse is needed. -/
theorem nonlinear_tendsto (n : ℕ) (x : Fin (2*(n+1)) → ℂ) :
    Tendsto (fun k => nonlinearReadout (n+1) k x) atTop
      (nhds (nativeSourceFiniteBoundaryEnergy (2*(n+1)) x/2-
        2*canonicalCompletedNativeLogDerivativeMoment 0*Complex.normSq (x 0))) := by
  have ht := nativeSourceProjectiveBoundaryJetSynthesis_energy_tendsto (n+1) x
  simp_rw [nativeSourceProjectiveBoundaryJetSynthesis_energy_eq_storage] at ht
  have hu := (ht.div_const 2).sub_const
    (2*canonicalCompletedNativeLogDerivativeMoment 0*Complex.normSq (x 0))
  apply hu.congr'
  filter_upwards [canonicalCompletedNativeRadialProjectiveChiral_eventually_regular (2*(n+1))]
    with k hk
  rw [storage_jet_euler_exact n k x (fun r => (hk r).2.1) (fun r => (hk r).2.2)]
  ring

/-- PR41 residuals: the limit is twice the algebraic pivot MINUS the exact
rank-one source contribution. The nonlinear term need not be nonnegative. -/
theorem pr41_nonlinear_tendsto (s : Fin 2) (n : ℕ) :
    Tendsto (fun k => nonlinearReadout (n+1) k (nativeResidualBoundary s n)) atTop
      (nhds (2*carryPairingPivot
        (hankelPairing (fun j => canonicalCompletedNativeLogDerivativeMoment (j+s.val))) n-
        2*canonicalCompletedNativeLogDerivativeMoment 0*
          Complex.normSq (nativeResidualBoundary s n 0))) := by
  have ht := nonlinear_tendsto n (nativeResidualBoundary s n)
  rw [nativeResidualBoundary_energy] at ht
  have he (d z t : ℝ) : 4*d/2-2*z*t = 2*d-2*z*t := by ring
  rw [he] at ht
  exact ht

/-- The Euler term on a PR41 even residual is determined by its constant
coefficient. No next-pivot sign is used to calculate it. -/
theorem pr41_even_euler_coefficient (n : ℕ) :
    Complex.normSq (nativeResidualBoundary 0 n 0) =
      ((orthogonalPolynomial canonicalCompletedNativeLogDerivativeMoment n).coeff 0)^2 := by
  simp [nativeResidualBoundary, nativeSourceBoundaryFromParity, Complex.normSq_ofReal,
    pow_two]

/-- The shifted sector has no zeroth jet, hence its Euler term vanishes
exactly. Positivity there must come from the full nonlinear source pairing. -/
theorem pr41_odd_euler_coefficient (n : ℕ) :
    Complex.normSq (nativeResidualBoundary 1 n 0) = 0 := by
  simp [nativeResidualBoundary, nativeSourceBoundaryFromParity]


end
end CarryResidualEuler
