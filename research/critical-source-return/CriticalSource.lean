import EighthReturnCheck
import CarrySelfAdjointOperator.NativeSourceAllOrderSchur

/-! Actual source coordinates for a Schur test. The incident and returned
vectors are synthesized by the existing finite-difference chart. No positive
port or contractivity premise enters their signed balance. -/
namespace CarryCriticalSource
open CarrySelfAdjointOperator CarrySelfAdjointOperator.ChiralReturn
open CarryReturnCompatibility Filter
open scoped BigOperators InnerProductSpace ComplexConjugate Topology Matrix
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

abbrev h := canonicalCompletedNativeLogDerivativeMoment

/-- Insert one real test in the inherited even or odd parity coordinates. -/
def parityCoordinates (s : Fin 2) {m : ℕ} (v : Fin m → ℝ) : Fin (2*m) → ℂ :=
  if s.val = 0 then nativeSourceBoundaryFromParity m (fun i => (v i : ℂ)) 0
  else nativeSourceBoundaryFromParity m 0 (fun i => (v i : ℂ))

private theorem real_quadratic_sum (s m : ℕ) (v : Fin m → ℝ) :
    (∑ i : Fin m, ∑ j : Fin m, h (i.val+j.val+s)*v i*v j) =
      sourceMomentQuadratic h s m v := by
  simp only [sourceMomentQuadratic, sourceMomentMatrix, dotProduct,
    Matrix.mulVec, Pi.star_apply, star_trivial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The factor four is inherited from the original alternating Green tower. -/
theorem parityCoordinates_boundary (s : Fin 2) (m : ℕ) (v : Fin m → ℝ) :
    nativeSourceFiniteBoundaryEnergy (2*m) (parityCoordinates s v) =
      4*sourceMomentQuadratic h s.val m v := by
  fin_cases s
  · change nativeSourceFiniteBoundaryEnergy (2*m)
      (nativeSourceBoundaryFromParity m (fun i => (v i : ℂ)) 0) =
        4*sourceMomentQuadratic h 0 m v
    rw [nativeSourceFiniteBoundaryEnergy_even_split,
      nativeSourceEvenBoundaryPhase_fromParity, nativeSourceOddBoundaryPhase_fromParity,
      primeDepthGeometricMoment_eq_canonical]
    simp only [Pi.zero_apply, map_zero, mul_zero, Complex.zero_re,
      Finset.sum_const_zero, add_zero, Complex.conj_ofReal, ← Complex.ofReal_mul,
      Complex.ofReal_re]
    congr 1
    simpa [h, Nat.add_zero, mul_assoc] using real_quadratic_sum 0 m v
  · change nativeSourceFiniteBoundaryEnergy (2*m)
      (nativeSourceBoundaryFromParity m 0 (fun i => (v i : ℂ))) =
        4*sourceMomentQuadratic h 1 m v
    rw [nativeSourceFiniteBoundaryEnergy_even_split,
      nativeSourceEvenBoundaryPhase_fromParity, nativeSourceOddBoundaryPhase_fromParity,
      primeDepthGeometricMoment_eq_canonical]
    simp only [Pi.zero_apply, map_zero, mul_zero, Complex.zero_re,
      Finset.sum_const_zero, zero_add, Complex.conj_ofReal, ← Complex.ofReal_mul,
      Complex.ofReal_re]
    congr 1
    simpa [h, mul_assoc] using real_quadratic_sum 1 m v

/-- The moments select a test combination, not the physical carrier. -/
def criticalCoefficients (s : Fin 2) (n : ℕ) : Fin (n+1) → ℝ :=
  Fin.snoc (-((sourceMomentMatrix h s.val n)⁻¹ *ᵥ sourceMomentCoupling h s.val n)) 1

def criticalCoordinates (s : Fin 2) (n : ℕ) : Fin (2*(n+1)) → ℂ :=
  parityCoordinates s (criticalCoefficients s n)

def criticalInput (s : Fin 2) (n k : ℕ) : Fin (2*(n+1)) → ℂ :=
  nativeSourceChiralJetInput (n+1) k (criticalCoordinates s n)

def criticalIncident (s : Fin 2) (n k : ℕ) : RadialIncidentSpan k (2*(n+1)) :=
  radialIncidentVector k (2*(n+1)) (criticalInput s n k)

def criticalReturned (s : Fin 2) (n k : ℕ) :
    CanonicalCompletedNativeChiralCauchyCarrier :=
  radialReturnTransfer k (2*(n+1)) (criticalIncident s n k)

def criticalBalance (s : Fin 2) (n k : ℕ) : ℝ :=
  ‖criticalIncident s n k‖^2-‖criticalReturned s n k‖^2

/-- Independent source directions, before any scalar projection. -/
def criticalPairing (s t : Fin 2) (n k : ℕ) : ℂ :=
  inner ℂ (criticalIncident s n k : CanonicalCompletedNativeChiralCauchyCarrier)
      (criticalIncident t n k : CanonicalCompletedNativeChiralCauchyCarrier) -
    inner ℂ (criticalReturned s n k) (criticalReturned t n k)

theorem criticalPairing_source (s t : Fin 2) (n k : ℕ)
    (hreg : ∀ i : Fin (2*(n+1)), completedNativePositiveHermiteBiehlerCoordinate
      (canonicalCompletedC3RadialTiltPoint k i) ≠ 0) :
    criticalPairing s t n k =
      polarizedSourceBalance k (criticalInput s n k) (criticalInput t n k) 1 1 :=
  radialReturnTransfer_polarized_balance k (2*(n+1)) _ _ hreg

theorem criticalPairing_self (s : Fin 2) (n k : ℕ) :
    criticalPairing s s n k = (criticalBalance s n k : ℂ) := by
  simp [criticalPairing, inner_self_eq_norm_sq_to_K, criticalBalance]

theorem criticalBalance_eq_storage (s : Fin 2) (n k : ℕ) :
    criticalBalance s n k = (storage k (criticalInput s n k) 1).re :=
  (storage_one_eq_finiteTransfer_energy k (2*(n+1)) _).symm

/-- Only the OLD prefix is positive. The new pivot may have any sign. -/
theorem criticalCoordinates_boundary (s : Fin 2) (n : ℕ)
    (hA : (sourceMomentMatrix h s.val n).PosDef) :
    nativeSourceFiniteBoundaryEnergy (2*(n+1)) (criticalCoordinates s n) =
      4*sourceMomentSchur h s.val n := by
  rw [criticalCoordinates, parityCoordinates_boundary]
  exact congrArg (4*·) (sourceMomentSchur_critical_direction h s.val n hA)

/-- Quantitative finite-regularization error, with the full original storage. -/
theorem criticalBalance_eventually_error (s : Fin 2) (n : ℕ)
    (hA : (sourceMomentMatrix h s.val n).PosDef) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ k : ℕ in atTop,
      |2*criticalBalance s n k-4*sourceMomentSchur h s.val n| ≤
        η*‖criticalCoordinates s n‖^2 := by
  filter_upwards [storage_one_chiralJetInput_eventually_energy_control (n+1) η hη]
    with k hk
  simpa only [criticalBalance_eq_storage, criticalInput,
    criticalCoordinates_boundary s n hA] using hk (criticalCoordinates s n)

/-- The exact next pivot is half the limiting physical incident-return balance. -/
theorem criticalBalance_tendsto (s : Fin 2) (n : ℕ)
    (hA : (sourceMomentMatrix h s.val n).PosDef) :
    Tendsto (criticalBalance s n) atTop (nhds (2*sourceMomentSchur h s.val n)) := by
  have ht : Tendsto (fun k => 2*(storage k (criticalInput s n k) 1).re)
      atTop (nhds (nativeSourceFiniteBoundaryEnergy (2*(n+1))
        (criticalCoordinates s n))) := by
    simpa only [criticalInput, nativeSourceProjectiveBoundaryJetSynthesis_energy_eq_storage]
      using nativeSourceProjectiveBoundaryJetSynthesis_energy_tendsto
        (n+1) (criticalCoordinates s n)
  rw [criticalCoordinates_boundary s n hA] at ht
  have hh := ht.div_const 2
  have he : 4*sourceMomentSchur h s.val n/2 = 2*sourceMomentSchur h s.val n := by ring
  rw [he] at hh
  simpa only [← criticalBalance_eq_storage,
    mul_div_cancel_left₀ _ (by norm_num : (2:ℝ) ≠ 0)] using hh

/-- The two Jordan channels are retained without a contractivity premise. -/
theorem criticalBalance_eq_jordan (s : Fin 2) (n k : ℕ) :
    criticalBalance s n k =
      ‖radialReturnJordanPositivePort k (2*(n+1)) (criticalIncident s n k)‖^2 -
      ‖radialReturnJordanNegativePort k (2*(n+1)) (criticalIncident s n k)‖^2 := by
  rw [criticalBalance_eq_storage]
  exact (radialReturnJordanPorts_storage k (2*(n+1)) (criticalInput s n k)).symm

end
end CarryCriticalSource
