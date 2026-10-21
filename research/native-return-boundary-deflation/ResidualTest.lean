import SchurLimit

namespace CarryReturnDeflation
open CarrySelfAdjointOperator ChiralReturn CarryPositiveSquare
open CarryJetOverlap CarryFiberTransport NativeMomentOrthogonalization
open GeometryOfNumbers.Analysis
open scoped InnerProductSpace ComplexConjugate BigOperators
open Filter Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

theorem canonical_even_real (n : ℕ) (a b : Fin n → ℝ) :
    canonicalBoundaryPair n
      (nativeSourceBoundaryFromParity n (fun i => (a i:ℂ)) 0)
      (nativeSourceBoundaryFromParity n (fun i => (b i:ℂ)) 0) =
      (momentForm canonicalCompletedNativeLogDerivativeMoment
        (coefficientPolynomial a) (coefficientPolynomial b):ℂ) := by
  rw [momentForm_coefficients]
  simp only [canonicalBoundaryPair,nativeSourceEvenBoundaryPhase_fromParity,
    nativeSourceOddBoundaryPhase_fromParity,Pi.zero_apply,map_zero,mul_zero,zero_mul,
    Finset.sum_const_zero,add_zero,Complex.conj_ofReal,carryPairingBilinear]
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem constant_coefficientPolynomial (n : ℕ) :
    coefficientPolynomial (Pi.single 0 1 : Fin (n+1) → ℝ) = 1 := by
  simp [coefficientPolynomial,Pi.single_apply,ite_smul]

/-- No sign assumption: algebraic orthogonality from PR41 is sufficient.
This is the SAME monic residual, not the nearby rational trial column. -/
theorem pr41_even_head_cross_zero (n : ℕ) (hn : 0 < n)
    (hp : ∀ r < n, carryPairingPivot (hankelPairing canonicalCompletedNativeLogDerivativeMoment) r ≠ 0) :
    canonicalBoundaryPair (n+1) (headBoundary n) (nativeResidualBoundary 0 n) = 0 := by
  unfold headBoundary nativeResidualBoundary
  have he := canonical_even_real (n+1) (Pi.single 0 1)
    (fun i => (orthogonalPolynomial canonicalCompletedNativeLogDerivativeMoment n).coeff i)
  have heq : (fun i : Fin (n+1) => (((Pi.single 0 (1:ℝ) : Fin (n+1) → ℝ) i):ℂ)) = (Pi.single 0 1 : Fin (n+1) → ℂ) := by
    funext i
    by_cases hi : i=0 <;> simp [hi]
  rw [heq] at he
  have hh := orthogonalPolynomial_orthogonal canonicalCompletedNativeLogDerivativeMoment n hp 0 hn
  have hz : orthogonalPolynomial canonicalCompletedNativeLogDerivativeMoment 0 = 1 := by
    simp [orthogonalPolynomial,residualPolynomial]
  rw [hz] at hh
  rw [constant_coefficientPolynomial,orthogonalPolynomial_from_coefficients,hh] at he
  simpa only [Fin.val_zero,Nat.add_zero,ite_true,Complex.ofReal_zero] using he

theorem pr41_odd_head_cross_zero (n : ℕ) :
    canonicalBoundaryPair (n+1) (headBoundary n) (nativeResidualBoundary 1 n) = 0 := by
  simp [canonicalBoundaryPair,headBoundary,nativeResidualBoundary]

/-- The derived physical remainder recovers the WHOLE canonical energy on
an input orthogonal to the original head. No sign is manufactured. -/
theorem head_orthogonal_remainder_tendsto (n : ℕ) (x y : Fin (2*(n+1)) → ℂ)
    (hx : canonicalBoundaryPair (n+1) (headBoundary n) x = 0) :
    Tendsto (fun k => jetSchurRemainder (n+1) k x y) atTop
      (nhds (2*canonicalBoundaryPair (n+1) x y)) := by
  have hh := jet_remaining_schur_tendsto n x y
  simpa only [hx,map_zero,zero_mul,zero_div,sub_zero] using hh

def projectedJetPair (n k : ℕ) (x y : Fin (2*n) → ℂ) : ℂ :=
  inner ℂ (jetBoundaryChannel n k x) (jetBoundaryChannel n k y)/(oneDeficit k:ℂ)

theorem projectedJetPair_eq_difference (n : ℕ) (x y : Fin (2*n) → ℂ) :
    ∀ᶠ k : ℕ in atTop, projectedJetPair n k x y =
      jetNativeBalance n k x y - jetSchurRemainder n k x y := by
  filter_upwards [oneDeficit_eventually_pos] with k hk
  have hh := native_balance_split k (2*n)
    (nativeSourceChiralJetInput n k x) (nativeSourceChiralJetInput n k y)
  have hd : (oneDeficit k:ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hk
  unfold projectedJetPair jetSchurRemainder jetBoundaryChannel jetRemainingPair jetNativeBalance
  field_simp [hd]
  linear_combination -hh

/-- The positive extracted part can vanish on the limiting critical
directions. Its positivity alone cannot certify the remaining pivot. -/
theorem head_orthogonal_projected_tendsto_zero (n : ℕ) (x y : Fin (2*(n+1)) → ℂ)
    (hx : canonicalBoundaryPair (n+1) (headBoundary n) x = 0) :
    Tendsto (fun k => projectedJetPair (n+1) k x y) atTop (nhds 0) := by
  have ht := (jetNativeBalance_tendsto (n+1) x y).sub
    (head_orthogonal_remainder_tendsto n x y hx)
  rw [sub_self] at ht
  exact ht.congr' (Filter.EventuallyEq.symm (projectedJetPair_eq_difference (n+1) x y))

theorem pr41_even_projected_tendsto_zero (n : ℕ) (hn : 0 < n)
    (hp : ∀ r < n, carryPairingPivot (hankelPairing canonicalCompletedNativeLogDerivativeMoment) r ≠ 0) :
    Tendsto (fun k => projectedJetPair (n+1) k (nativeResidualBoundary 0 n)
      (nativeResidualBoundary 0 n)) atTop (nhds 0) :=
  head_orthogonal_projected_tendsto_zero n _ _ (pr41_even_head_cross_zero n hn hp)

theorem pr41_odd_projected_tendsto_zero (n : ℕ) :
    Tendsto (fun k => projectedJetPair (n+1) k (nativeResidualBoundary 1 n)
      (nativeResidualBoundary 1 n)) atTop (nhds 0) :=
  head_orthogonal_projected_tendsto_zero n _ _ (pr41_odd_head_cross_zero n)

theorem deflatedJetEnergy_eq_parts (n k : ℕ) (x : Fin (2*n) → ℂ) :
    deflatedJetEnergy n k x =
      (projectedJetPair n k x x).re + (jetSchurRemainder n k x x).re := by
  simp only [deflatedJetEnergy,projectedJetPair,jetSchurRemainder,
    Complex.div_ofReal_re,physical_inner_self_re,add_div]

theorem residual_energy_tendsto_of_projected_zero (s : Fin 2) (n : ℕ)
    (hz : Tendsto (fun k => projectedJetPair (n+1) k (nativeResidualBoundary s n)
      (nativeResidualBoundary s n)) atTop (nhds 0)) :
    Tendsto (fun k => (jetSchurRemainder (n+1) k (nativeResidualBoundary s n)
      (nativeResidualBoundary s n)).re) atTop
      (nhds (2*carryPairingPivot
        (hankelPairing (fun j => canonicalCompletedNativeLogDerivativeMoment (j+s.val))) n)) := by
  have ht := (pr41_deflatedJetEnergy_tendsto s n).sub
    (Complex.continuous_re.continuousAt.tendsto.comp hz)
  simp only [Complex.zero_re,sub_zero] at ht
  convert ht using 1
  funext k
  rw [deflatedJetEnergy_eq_parts]
  simp only [Function.comp_apply]
  ring

theorem pr41_even_remaining_energy_tendsto (n : ℕ) (hn : 0 < n)
    (hp : ∀ r < n, carryPairingPivot (hankelPairing canonicalCompletedNativeLogDerivativeMoment) r ≠ 0) :
    Tendsto (fun k => (jetSchurRemainder (n+1) k (nativeResidualBoundary 0 n)
      (nativeResidualBoundary 0 n)).re) atTop
      (nhds (2*carryPairingPivot (hankelPairing canonicalCompletedNativeLogDerivativeMoment) n)) := by
  simpa only [Fin.val_zero,Nat.add_zero] using
    residual_energy_tendsto_of_projected_zero 0 n (pr41_even_projected_tendsto_zero n hn hp)

theorem pr41_odd_remaining_energy_tendsto (n : ℕ) :
    Tendsto (fun k => (jetSchurRemainder (n+1) k (nativeResidualBoundary 1 n)
      (nativeResidualBoundary 1 n)).re) atTop
      (nhds (2*carryPairingPivot
        (hankelPairing (fun j => canonicalCompletedNativeLogDerivativeMoment (j+1))) n)) := by
  simpa only [Fin.val_one] using
    residual_energy_tendsto_of_projected_zero 1 n (pr41_odd_projected_tendsto_zero n)

end
end CarryReturnDeflation
