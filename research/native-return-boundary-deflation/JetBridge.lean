import NativeDeflation

namespace CarryReturnDeflation
open CarrySelfAdjointOperator ChiralReturn CarryPositiveSquare
open CarryJetOverlap CarryFiberTransport CarryResidualEuler NativeMomentOrthogonalization
open scoped InnerProductSpace ComplexConjugate BigOperators
open Filter Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

def jetBoundaryChannel (n k : ℕ) (x : Fin (2*n) → ℂ) : Physical :=
  boundaryChannel k (2*n) (nativeSourceChiralJetInput n k x)
def jetRemainingPair (n k : ℕ) (x y : Fin (2*n) → ℂ) : ℂ :=
  remainingPair k (2*n) (nativeSourceChiralJetInput n k x) (nativeSourceChiralJetInput n k y)

/-- All complete jets are synthesized first. This exposes the exact native
positive boundary channel and the remaining signed physical pair. -/
theorem jet_deflation_balance (n k : ℕ) (x y : Fin (2*n) → ℂ)
    (hs : strip k (2*n))
    (hp : ∀ i : Fin (2*n), completedNativePositiveHermiteBiehlerCoordinate (radialPoint k i) ≠ 0) :
    (oneDeficit k:ℂ)*(2*jetBudget n k x y hs) =
      inner ℂ (jetBoundaryChannel n k x) (jetBoundaryChannel n k y) + jetRemainingPair n k x y := by
  have hh := native_balance_split k (2*n)
    (nativeSourceChiralJetInput n k x) (nativeSourceChiralJetInput n k y)
  have hb := radialReturnTransfer_polarized_balance k (2*n)
    (nativeSourceChiralJetInput n k x) (nativeSourceChiralJetInput n k y) hp
  rw [radialIncidentVector_coe,radialIncidentVector_coe,
    radialReturnTransfer_exact,radialReturnTransfer_exact] at hb
  change nativeBalance k (2*n) (nativeSourceChiralJetInput n k x)
    (nativeSourceChiralJetInput n k y) = _ at hb
  have he : nativeBalance k (2*n) (nativeSourceChiralJetInput n k x)
      (nativeSourceChiralJetInput n k y) = 2*jetBudget n k x y hs := by
    rw [hb,jetBudget_eq_original_pairing n k x y hs hp,jet_pairing_source_balance n k x y hp]
    ring
  rw [he] at hh
  exact hh

/-- The WHOLE normalized split, before any sign conclusion about its pieces. -/
def deflatedJetEnergy (n k : ℕ) (x : Fin (2*n) → ℂ) : ℝ :=
  (‖jetBoundaryChannel n k x‖^2 + (jetRemainingPair n k x x).re) / oneDeficit k

theorem deflatedJetEnergy_eventually_storage (n : ℕ) (x : Fin (2*n) → ℂ) :
    ∀ᶠ k : ℕ in atTop, deflatedJetEnergy n k x =
      (storage k (nativeSourceChiralJetInput n k x) 1).re := by
  filter_upwards [oneDeficit_eventually_pos] with k hk
  unfold deflatedJetEnergy jetBoundaryChannel jetRemainingPair
  rw [← native_energy_split]
  exact mul_div_cancel_left₀ _ (ne_of_gt hk)

/-- The new decomposition retains the original finite boundary energy in
the limit. No separate limit of the positive and signed pieces is assumed. -/
theorem deflatedJetEnergy_tendsto (n : ℕ) (x : Fin (2*n) → ℂ) :
    Tendsto (fun k => deflatedJetEnergy n k x) atTop
      (nhds (nativeSourceFiniteBoundaryEnergy (2*n) x/2)) := by
  have hh := nativeSourceProjectiveBoundaryJetSynthesis_energy_tendsto n x
  simp_rw [nativeSourceProjectiveBoundaryJetSynthesis_energy_eq_storage] at hh
  have ht := hh.div_const 2
  have he (a : ℝ) : 2*a/2=a := by ring
  simp_rw [he] at ht
  exact ht.congr' (Filter.EventuallyEq.symm (deflatedJetEnergy_eventually_storage n x))

/-- Exact PR41 residual, BOTH sectors and every order. No preceding or new
pivot sign is a hypothesis. The remaining sign problem has not been erased. -/
theorem pr41_deflatedJetEnergy_tendsto (s : Fin 2) (n : ℕ) :
    Tendsto (fun k => deflatedJetEnergy (n+1) k (nativeResidualBoundary s n)) atTop
      (nhds (2*GeometryOfNumbers.Analysis.carryPairingPivot
        (hankelPairing (fun j => canonicalCompletedNativeLogDerivativeMoment (j+s.val))) n)) := by
  have ht := deflatedJetEnergy_tendsto (n+1) (nativeResidualBoundary s n)
  rw [nativeResidualBoundary_energy] at ht
  have he (a : ℝ) : 4*a/2=2*a := by ring
  simpa only [he] using ht

/-- The specific exact even residual requested in the PR49 recommendation,
now transported through the PHYSICAL boundary decomposition. No rational
trial direction is substituted for it. -/
theorem exact_seventh_residual_test :
    Tendsto (fun k => deflatedJetEnergy 7 k (nativeResidualBoundary 0 6)) atTop
      (nhds (2*GeometryOfNumbers.Analysis.carryPairingPivot
        (hankelPairing canonicalCompletedNativeLogDerivativeMoment) 6)) := by
  simpa only [Fin.val_zero, Nat.add_zero] using pr41_deflatedJetEnergy_tendsto 0 6

end
end CarryReturnDeflation
