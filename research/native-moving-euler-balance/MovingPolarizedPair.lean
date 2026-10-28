import PolarizedBoundaryReadout

namespace CarryMovingEulerBalance
open CarrySelfAdjointOperator CarryNativeBinomial CarryEulerNewtonAll
open CarryNativeTfvd CarryCriticalTfvd CarryCommutatorControl CarryStencilBoundary
open CarrySpatialCorrection CarryEnergyCorrection CarryOddEnergy CarryMixedParity CarryCrossRadial CarryGreenLeading CarryGreenCubic CarryOddGreen CarryCubicOdd CarryCurvatureGreen CarryOddCauchy CarryCriticalGrid NativeLaguerre NativeCauchyPorts
open CarryAddressSplit CarryPrincipalFlow CarryTailReturn CarryBoundaryMargin CarryCriticalComplete
open CarrySelfAdjointOperator.ChiralReturn CarrySelfAdjointOperator.PhysicalSewing
open Filter Topology
open scoped BigOperators ComplexConjugate InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- Moving complex coefficient families; every finite-step ordered crossing
is retained until the EXISTING polarized jet-kernel limit is applied. -/
theorem native_moving_pairing_tendsto (n : ℕ)
    (y z : ℕ → Fin (2*n) → ℂ) (u v : Fin (2*n) → ℂ)
    (hy : Tendsto y atTop (nhds u)) (hz : Tendsto z atTop (nhds v)) :
    Tendsto (fun k => canonicalCompletedNativeProjectiveChiralForm
      (nativeSourceProjectiveBoundaryJetSynthesis n k (y k))
      (nativeSourceProjectiveBoundaryJetSynthesis n k (z k))) atTop
      (nhds (originalBoundaryPair n u v)) := by
  let order : Fin n ⊕ Fin n → ℕ := Sum.elim (fun i => 2*(i:ℕ)) (fun i => 2*(i:ℕ)+1)
  let coeff : (Fin (2*n) → ℂ) → (Fin n ⊕ Fin n → ℂ) :=
    fun x => Sum.elim (nativeSourceEvenBoundaryPhase n x) (nativeSourceOddBoundaryPhase n x)
  have hc (f : ℕ → Fin (2*n) → ℂ) (a : Fin (2*n) → ℂ)
      (hf : Tendsto f atTop (nhds a)) (i : Fin n ⊕ Fin n) :
      Tendsto (fun k => coeff (f k) i) atTop (nhds (coeff a i)) := by
    cases i with
    | inl i => simpa only [coeff, Sum.elim_inl, nativeSourceEvenBoundaryPhase] using
        tendsto_const_nhds.mul ((tendsto_pi_nhds.1 hf) (nativeSourceEvenBoundaryIndex n i))
    | inr i => simpa only [coeff, Sum.elim_inr, nativeSourceOddBoundaryPhase] using
        tendsto_const_nhds.mul ((tendsto_pi_nhds.1 hf) (nativeSourceOddBoundaryIndex n i))
  have he (k : ℕ) : canonicalCompletedNativeProjectiveChiralForm
      (nativeSourceProjectiveBoundaryJetSynthesis n k (y k))
      (nativeSourceProjectiveBoundaryJetSynthesis n k (z k))=
      ∑ i : Fin n ⊕ Fin n, ∑ j : Fin n ⊕ Fin n,
        conj (coeff (y k) i)*coeff (z k) j*
          canonicalCompletedNativeProjectiveChiralForm
            (projectiveChiralDifferenceJet k (order i)) (projectiveChiralDifferenceJet k (order j)) :=
    nativeSourceProjectiveBoundaryJetSynthesis_pairing n k (y k) (z k)
  have ht : Tendsto (fun k => canonicalCompletedNativeProjectiveChiralForm
      (nativeSourceProjectiveBoundaryJetSynthesis n k (y k))
      (nativeSourceProjectiveBoundaryJetSynthesis n k (z k))) atTop
      (nhds (∑ i : Fin n ⊕ Fin n, ∑ j : Fin n ⊕ Fin n,
        conj (coeff u i)*coeff v j*
          polarizedGreenMomentCoefficient primeDepthGeometricMoment (order i) (order j))) := by
    simp_rw [he]
    apply tendsto_finsetSum
    intro i _
    apply tendsto_finsetSum
    intro j _
    exact ((Complex.continuous_conj.continuousAt.tendsto.comp (hc y u hy i)).mul
      (hc z v hz j)).mul
        (projectiveChiralDifferenceJet_pairing_tendsto_primeDepthCoefficient (order i) (order j))
  simpa only [Fintype.sum_sum_type, order, coeff, Sum.elim_inl, Sum.elim_inr,
    polarizedGreenMomentCoefficient_even_even, polarizedGreenMomentCoefficient_odd_odd,
    polarizedGreenMomentCoefficient_even_odd, polarizedGreenMomentCoefficient_odd_even,
    mul_zero, Finset.sum_const_zero, add_zero, zero_add] using ht

/-- Two independently moving ORIGINAL sources, after complete vector sewing. -/
theorem physical_moving_pairing_tendsto (n : ℕ) (x z : ℕ → ℕ →₀ ℂ)
    (u v : Fin (2*n) → ℂ)
    (hx : ∀ᶠ k : ℕ in atTop, (x k).support ⊆ Finset.range (2*n))
    (hz : ∀ᶠ k : ℕ in atTop, (z k).support ⊆ Finset.range (2*n))
    (hu : Tendsto (fun k => physicalEulerChart n k (x k)) atTop (nhds u))
    (hv : Tendsto (fun k => physicalEulerChart n k (z k)) atTop (nhds v)) :
    Tendsto (fun k => canonicalCompletedNativeProjectiveChiralForm
      (physicalCompletedFiniteSource k (x k)) (physicalCompletedFiniteSource k (z k))) atTop
      (nhds (originalBoundaryPair n (eulerNewton (2*n) 0 u) (eulerNewton (2*n) 0 v))) := by
  have hy := source_newton_path_tendsto n x u hu
  have hw := source_newton_path_tendsto n z v hv
  rw [← euler_newton_at_zero] at hy hw
  have ht := native_moving_pairing_tendsto n _ _ _ _ hy hw
  have he : (fun k => canonicalCompletedNativeProjectiveChiralForm
      (nativeSourceProjectiveBoundaryJetSynthesis n k (newtonCoordinates n k (fun r : Fin (2*n) => x k r)))
      (nativeSourceProjectiveBoundaryJetSynthesis n k (newtonCoordinates n k (fun r : Fin (2*n) => z k r))))
      =ᶠ[atTop] (fun k => canonicalCompletedNativeProjectiveChiralForm
        (physicalCompletedFiniteSource k (x k)) (physicalCompletedFiniteSource k (z k))) := by
    filter_upwards [hx,hz] with k hk hl
    rw [← physical_source_newton_all_order n k (x k) hk,
      ← physical_source_newton_all_order n k (z k) hl]
  exact ht.congr' he

theorem physical_green_pairing_tendsto (eta : ℝ) (h0 : 0<eta) (h1 : eta<1)
    (n : ℕ) (x z : ℕ → ℕ →₀ ℂ) (u v : Fin (2*n) → ℂ)
    (hx : ∀ᶠ k : ℕ in atTop, (x k).support ⊆ Finset.range (2*n))
    (hz : ∀ᶠ k : ℕ in atTop, (z k).support ⊆ Finset.range (2*n))
    (hu : Tendsto (fun k => physicalEulerChart n k (x k)) atTop (nhds u))
    (hv : Tendsto (fun k => physicalEulerChart n k (z k)) atTop (nhds v)) :
    Tendsto (fun k => crossGreenPair eta h0 h1 k k (x k) (z k)) atTop
      (nhds (originalBoundaryPair n (eulerNewton (2*n) 0 u) (eulerNewton (2*n) 0 v))) := by
  simpa only [cross_green_eq_original] using physical_moving_pairing_tendsto n x z u v hx hz hu hv

/-- The same complex physical limit, in the original Euler boundary coordinates. -/
theorem physical_green_pairing_euler_tendsto (eta : ℝ) (h0 : 0<eta) (h1 : eta<1)
    (n : ℕ) (x z : ℕ → ℕ →₀ ℂ) (u v : Fin (2*n) → ℂ)
    (hx : ∀ᶠ k : ℕ in atTop, (x k).support ⊆ Finset.range (2*n))
    (hz : ∀ᶠ k : ℕ in atTop, (z k).support ⊆ Finset.range (2*n))
    (hu : Tendsto (fun k => physicalEulerChart n k (x k)) atTop (nhds u))
    (hv : Tendsto (fun k => physicalEulerChart n k (z k)) atTop (nhds v)) :
    Tendsto (fun k => crossGreenPair eta h0 h1 k k (x k) (z k)) atTop
      (nhds (2*originalBoundaryPair n u v)) := by
  simpa only [original_boundary_pair_euler_zero] using
    physical_green_pairing_tendsto eta h0 h1 n x z u v hx hz hu hv

end
end CarryMovingEulerBalance
