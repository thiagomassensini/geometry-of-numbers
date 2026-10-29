import JetBridge

namespace CarryReturnDeflation
open CarrySelfAdjointOperator ChiralReturn CarryPositiveSquare
open CarryJetOverlap CarryFiberTransport NativeMomentOrthogonalization
open scoped InnerProductSpace ComplexConjugate BigOperators
open Filter Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000

/-- The already existing polarized canonical boundary kernel, retaining both
parities and both independently synthesized coefficient families. -/
def canonicalBoundaryPair (n : ℕ) (x y : Fin (2*n) → ℂ) : ℂ :=
  (∑ i : Fin n, ∑ j : Fin n,
    conj (nativeSourceEvenBoundaryPhase n x i)*nativeSourceEvenBoundaryPhase n y j*
      (canonicalCompletedNativeLogDerivativeMoment (i+j):ℂ)) +
  ∑ i : Fin n, ∑ j : Fin n,
    conj (nativeSourceOddBoundaryPhase n x i)*nativeSourceOddBoundaryPhase n y j*
      (canonicalCompletedNativeLogDerivativeMoment (i+j+1):ℂ)

def jetNativeBalance (n k : ℕ) (x y : Fin (2*n) → ℂ) : ℂ :=
  nativeBalance k (2*n) (nativeSourceChiralJetInput n k x) (nativeSourceChiralJetInput n k y)

theorem jetNativeBalance_eq_form (n k : ℕ) (x y : Fin (2*n) → ℂ) :
    jetNativeBalance n k x y = 2*canonicalCompletedNativeProjectiveChiralForm
      (nativeSourceProjectiveBoundaryJetSynthesis n k x)
      (nativeSourceProjectiveBoundaryJetSynthesis n k y) := by
  rw [nativeSourceProjectiveBoundaryJetSynthesis_eq_originalSource,
    nativeSourceProjectiveBoundaryJetSynthesis_eq_originalSource]
  unfold jetNativeBalance nativeBalance balance canonicalCompletedNativeProjectiveChiralForm
  dsimp only
  ring

theorem jetNativeBalance_tendsto (n : ℕ) (x y : Fin (2*n) → ℂ) :
    Tendsto (fun k => jetNativeBalance n k x y) atTop (nhds (2*canonicalBoundaryPair n x y)) := by
  have ht := (nativeSourceProjectiveBoundaryJetSynthesis_pairing_tendsto n x y).const_mul (2:ℂ)
  simpa only [canonicalBoundaryPair, primeDepthGeometricMoment_eq_canonical,
    jetNativeBalance_eq_form] using ht

def headBoundary (n : ℕ) : Fin (2*(n+1)) → ℂ :=
  nativeSourceBoundaryFromParity (n+1) (Pi.single 0 1) 0

theorem headBoundary_eq_single (n : ℕ) : headBoundary n = Pi.single 0 1 := by
  funext a
  unfold headBoundary nativeSourceBoundaryFromParity
  by_cases ha : a=0
  · subst a; simp
  · by_cases he : a.val%2=0
    · have hn : a.val/2 ≠ 0 := by
        have hav : a.val ≠ 0 := by intro hh; exact ha (Fin.ext hh)
        omega
      have hf : (⟨a.val/2, by omega⟩ : Fin (n+1)) ≠ 0 := by
        intro hh; exact hn (congrArg Fin.val hh)
      simp [he,ha,hf]
    · simp [he,ha]

def headAmplitude (k : ℕ) : ℂ :=
  completedNativeNormalizedPositiveChiralAmplitude (radialPoint k 0)

theorem head_jet_input (n k : ℕ) :
    nativeSourceChiralJetInput (n+1) k (headBoundary n) = headAmplitude k • Pi.single 0 1 := by
  rw [headBoundary_eq_single]
  funext r
  simp only [nativeSourceChiralJetInput, LinearMap.coe_mk, AddHom.coe_mk]
  simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  by_cases hr : r=0
  · subst r
    simp [nativeSourceChiralJetInputMatrix,nativeSourceJetOrderPhase,
      completedGreenForwardWeight,headAmplitude]
  · have hv : 0 < r.val := by have := Fin.pos_iff_ne_zero.mpr hr; exact this
    simp [nativeSourceChiralJetInputMatrix,nativeSourceJetOrderPhase,
      completedGreenForwardWeight,headAmplitude,hr,
      Nat.choose_eq_zero_of_lt hv]

theorem head_jet_incident (n k : ℕ) :
    radialIncidentSynthesis k (2*(n+1)) (nativeSourceChiralJetInput (n+1) k (headBoundary n)) =
      headAmplitude k • nativeAnchor k := by
  rw [head_jet_input,map_smul]
  simp [radialIncidentSynthesis,nativeAnchor]

theorem head_jet_returned (n k : ℕ) :
    radialReturnedSynthesis k (2*(n+1)) (nativeSourceChiralJetInput (n+1) k (headBoundary n)) =
      headAmplitude k • (oneReturn k • nativeAnchor k) := by
  rw [head_jet_input,map_smul]
  simp [radialReturnedSynthesis,completedNativeRadialChiralMultiplierState,nativeAnchor,oneReturn]

theorem head_canonical_pair_self (n : ℕ) :
    canonicalBoundaryPair (n+1) (headBoundary n) (headBoundary n) =
      (canonicalCompletedNativeLogDerivativeMoment 0:ℂ) := by
  simp only [canonicalBoundaryPair,headBoundary,nativeSourceEvenBoundaryPhase_fromParity,
    nativeSourceOddBoundaryPhase_fromParity]
  simp [Pi.single_apply, apply_ite, ite_mul]

/-- A full source-dependent cutoff is allowed. The central scalar is
nonzero eventually because the ORIGINAL h0 is positive, not because later
Hankel pivots or a fitted Gram are positive. -/
theorem head_amplitude_eventually_ne_zero (n : ℕ) :
    ∀ᶠ k : ℕ in atTop, headAmplitude k ≠ 0 := by
  have ht := jetNativeBalance_tendsto (n+1) (headBoundary n) (headBoundary n)
  rw [head_canonical_pair_self] at ht
  have hz : (2:ℂ)*(canonicalCompletedNativeLogDerivativeMoment 0:ℂ) ≠ 0 := by
    exact mul_ne_zero (by norm_num) (by exact_mod_cast ne_of_gt canonicalCompletedNativeLogDerivativeMoment_zero_pos)
  have hn := ht.eventually_ne hz
  filter_upwards [hn] with k hk
  intro ha
  apply hk
  unfold jetNativeBalance nativeBalance balance
  simp_rw [head_jet_incident,head_jet_returned,ha]
  simp

def jetSchurRemainder (n k : ℕ) (x y : Fin (2*n) → ℂ) : ℂ :=
  jetRemainingPair n k x y / (oneDeficit k:ℂ)

/-- Exact realization of the FIRST Schur subtraction by physical channels.
No positivity of the remaining kernel is assumed or concluded. -/
theorem jet_remaining_schur_eventually (n : ℕ) (x y : Fin (2*(n+1)) → ℂ) :
    ∀ᶠ k : ℕ in atTop,
      jetSchurRemainder (n+1) k x y = jetNativeBalance (n+1) k x y -
        conj (jetNativeBalance (n+1) k (headBoundary n) x)*
          jetNativeBalance (n+1) k (headBoundary n) y /
          jetNativeBalance (n+1) k (headBoundary n) (headBoundary n) := by
  filter_upwards [oneDeficit_eventually_pos,head_amplitude_eventually_ne_zero n] with k hk ha
  have hs := native_schur_remainder k (2*(n+1))
    (nativeSourceChiralJetInput (n+1) k x) (nativeSourceChiralJetInput (n+1) k y) (ne_of_gt hk)
  have hd : deficit (oneReturn k) ≠ 0 := by
    rw [native_deficit]; exact_mod_cast ne_of_gt hk
  have he := scaled_anchor_schur (nativeAnchor k)
    (radialIncidentSynthesis k (2*(n+1)) (nativeSourceChiralJetInput (n+1) k x))
    (radialReturnedSynthesis k (2*(n+1)) (nativeSourceChiralJetInput (n+1) k x))
    (radialIncidentSynthesis k (2*(n+1)) (nativeSourceChiralJetInput (n+1) k y))
    (radialReturnedSynthesis k (2*(n+1)) (nativeSourceChiralJetInput (n+1) k y))
    (oneReturn k) (headAmplitude k) (anchorMass k) (ne_of_gt (anchorMass_pos k))
    (nativeAnchor_inner k) hd ha
  rw [native_deficit] at he
  unfold jetSchurRemainder jetRemainingPair jetNativeBalance nativeBalance
  simp_rw [head_jet_incident,head_jet_returned]
  rw [he]
  exact hs

theorem jet_remaining_schur_tendsto (n : ℕ) (x y : Fin (2*(n+1)) → ℂ) :
    Tendsto (fun k => jetSchurRemainder (n+1) k x y) atTop
      (nhds (2*(canonicalBoundaryPair (n+1) x y -
        conj (canonicalBoundaryPair (n+1) (headBoundary n) x)*
          canonicalBoundaryPair (n+1) (headBoundary n) y /
          (canonicalCompletedNativeLogDerivativeMoment 0:ℂ)))) := by
  have hs := jetNativeBalance_tendsto (n+1) x y
  have hx := jetNativeBalance_tendsto (n+1) (headBoundary n) x
  have hy := jetNativeBalance_tendsto (n+1) (headBoundary n) y
  have hh := jetNativeBalance_tendsto (n+1) (headBoundary n) (headBoundary n)
  rw [head_canonical_pair_self] at hh
  have hn : (2:ℂ)*(canonicalCompletedNativeLogDerivativeMoment 0:ℂ) ≠ 0 :=
    mul_ne_zero (by norm_num) (by exact_mod_cast ne_of_gt canonicalCompletedNativeLogDerivativeMoment_zero_pos)
  have ht := hs.sub (((continuous_star.tendsto _).comp hx).mul hy |>.div hh hn)
  have hzero : (canonicalCompletedNativeLogDerivativeMoment 0:ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt canonicalCompletedNativeLogDerivativeMoment_zero_pos
  have halg (a b c : ℂ) : 2*a - conj (2*b)*(2*c)/(2*(canonicalCompletedNativeLogDerivativeMoment 0:ℂ)) =
      2*(a-conj b*c/(canonicalCompletedNativeLogDerivativeMoment 0:ℂ)) := by
    simp only [map_mul, map_ofNat]
    field_simp [hzero]
  change Tendsto (fun k => jetNativeBalance (n+1) k x y -
      conj (jetNativeBalance (n+1) k (headBoundary n) x)*
        jetNativeBalance (n+1) k (headBoundary n) y /
        jetNativeBalance (n+1) k (headBoundary n) (headBoundary n)) atTop
    (nhds (2*canonicalBoundaryPair (n+1) x y -
      conj (2*canonicalBoundaryPair (n+1) (headBoundary n) x)*
        (2*canonicalBoundaryPair (n+1) (headBoundary n) y) /
        (2*(canonicalCompletedNativeLogDerivativeMoment 0:ℂ)))) at ht
  rw [halg] at ht
  exact ht.congr' (Filter.EventuallyEq.symm (jet_remaining_schur_eventually n x y))

end
end CarryReturnDeflation
