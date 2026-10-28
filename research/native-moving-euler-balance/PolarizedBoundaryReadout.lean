import MovingBalanceLimit

namespace CarryMovingEulerBalance
open CarrySelfAdjointOperator CarryEulerNewtonAll
open CarrySelfAdjointOperator.NativeLaguerre
open Filter Topology
open scoped BigOperators ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- A transparent name for the EXACT preexisting limit expression in
nativeSourceProjectiveBoundaryJetSynthesis_pairing_tendsto. No kernel is fitted. -/
abbrev originalBoundaryPair (n : ℕ) (x y : Fin (2*n) → ℂ) : ℂ :=
  (∑ i : Fin n, ∑ j : Fin n,
    conj (nativeSourceEvenBoundaryPhase n x i)*nativeSourceEvenBoundaryPhase n y j*
      (primeDepthGeometricMoment ((i:ℕ)+(j:ℕ)):ℂ)) +
  ∑ i : Fin n, ∑ j : Fin n,
    conj (nativeSourceOddBoundaryPhase n x i)*nativeSourceOddBoundaryPhase n y j*
      (primeDepthGeometricMoment ((i:ℕ)+(j:ℕ)+1):ℂ)

theorem original_boundary_pair_continuous (n : ℕ) :
    Continuous (fun p : (Fin (2*n) → ℂ) × (Fin (2*n) → ℂ) => originalBoundaryPair n p.1 p.2) := by
  unfold originalBoundaryPair nativeSourceEvenBoundaryPhase nativeSourceOddBoundaryPhase
  fun_prop

/-- Normalization is fixed by the two OLD limits of the SAME synthesized
state: four times this real diagonal is the original native boundary energy. -/
theorem original_boundary_pair_diagonal (n : ℕ) (y : Fin (2*n) → ℂ) :
    4*(originalBoundaryPair n y y).re=nativeSourceFiniteBoundaryEnergy (2*n) y := by
  have hp := (Complex.continuous_re.continuousAt.tendsto.comp
    (nativeSourceProjectiveBoundaryJetSynthesis_pairing_tendsto n y y)).const_mul (4:ℝ)
  have he := nativeSourceProjectiveBoundaryJetSynthesis_energy_tendsto n y
  simp only [← nativeSourceProjectiveBoundaryJetSynthesis_energy] at he
  exact tendsto_nhds_unique hp he

private theorem even_limit_phase (j : ℕ) :
    nativeSourceJetOrderPhase (2*j)*Complex.I^(2*j)=1 := by
  have hd : (2*j)/2=j := by omega
  simp only [nativeSourceJetOrderPhase, hd, Complex.ofReal_pow, Complex.ofReal_neg,
    Complex.ofReal_one, pow_mul, Complex.I_sq]
  rw [← mul_pow]
  norm_num

private theorem odd_limit_phase (j : ℕ) :
    nativeSourceJetOrderPhase (2*j+1)*Complex.I^(2*j+1)=Complex.I := by
  have hp : nativeSourceJetOrderPhase (2*j+1)=nativeSourceJetOrderPhase (2*j) := by
    unfold nativeSourceJetOrderPhase
    rw [show (2*j+1)/2=j from by omega, show (2*j)/2=j from by omega]
  rw [hp, pow_add, pow_one, ← mul_assoc, even_limit_phase, one_mul]

/-- Exact normalization of the ORIGINAL polarized boundary form under T_0.
Odd phases cancel in the complex pairing only after the proved sector limit. -/
theorem original_boundary_pair_euler_zero (n : ℕ) (x y : Fin (2*n) → ℂ) :
    originalBoundaryPair n (eulerNewton (2*n) 0 x) (eulerNewton (2*n) 0 y)=
      2*originalBoundaryPair n x y := by
  have he (v : Fin (2*n) → ℂ) (i : Fin n) :
      nativeSourceEvenBoundaryPhase n (eulerNewton (2*n) 0 v) i=
        (Real.sqrt 2:ℂ)*nativeSourceEvenBoundaryPhase n v i := by
    simp only [nativeSourceEvenBoundaryPhase, euler_newton_at_zero]
    change (((-1:ℝ)^(i:ℕ):ℝ):ℂ)*
      ((Real.sqrt 2:ℂ)*nativeSourceJetOrderPhase (2*(i:ℕ))*Complex.I^(2*(i:ℕ))*
        v (nativeSourceEvenBoundaryIndex n i))=_
    linear_combination (Real.sqrt 2:ℂ)*(((-1:ℝ)^(i:ℕ):ℝ):ℂ)*
      v (nativeSourceEvenBoundaryIndex n i)*(even_limit_phase (i:ℕ))
  have ho (v : Fin (2*n) → ℂ) (i : Fin n) :
      nativeSourceOddBoundaryPhase n (eulerNewton (2*n) 0 v) i=
        (Real.sqrt 2:ℂ)*Complex.I*nativeSourceOddBoundaryPhase n v i := by
    simp only [nativeSourceOddBoundaryPhase, euler_newton_at_zero]
    change (((-1:ℝ)^(i:ℕ):ℝ):ℂ)*
      ((Real.sqrt 2:ℂ)*nativeSourceJetOrderPhase (2*(i:ℕ)+1)*Complex.I^(2*(i:ℕ)+1)*
        v (nativeSourceOddBoundaryIndex n i))=_
    linear_combination (Real.sqrt 2:ℂ)*(((-1:ℝ)^(i:ℕ):ℝ):ℂ)*
      v (nativeSourceOddBoundaryIndex n i)*(odd_limit_phase (i:ℕ))
  have hs : (Real.sqrt 2:ℂ)^2=2 := by
    exact_mod_cast (Real.sq_sqrt (by norm_num : (0:ℝ)≤2))
  have ht (a b c : ℂ) :
      conj ((Real.sqrt 2:ℂ)*a)*((Real.sqrt 2:ℂ)*b)*c=2*(conj a*b*c) := by
    simp only [map_mul, Complex.conj_ofReal]
    linear_combination conj a*b*c*hs
  have hi (a b c : ℂ) :
      conj ((Real.sqrt 2:ℂ)*Complex.I*a)*((Real.sqrt 2:ℂ)*Complex.I*b)*c=
        2*(conj a*b*c) := by
    rw [mul_assoc (Real.sqrt 2:ℂ), mul_assoc (Real.sqrt 2:ℂ), ht]
    simp only [map_mul, Complex.conj_I]
    ring_nf
    norm_num [Complex.I_sq]
  unfold originalBoundaryPair
  simp only [he,ho,ht,hi]
  simp only [mul_add, Finset.mul_sum]

theorem boundary_energy_euler_zero (n : ℕ) (w : Fin (2*n) → ℂ) :
    nativeSourceFiniteBoundaryEnergy (2*n) (eulerNewton (2*n) 0 w)=
      2*nativeSourceFiniteBoundaryEnergy (2*n) w := by
  rw [← original_boundary_pair_diagonal n (eulerNewton (2*n) 0 w),
    original_boundary_pair_euler_zero, ← original_boundary_pair_diagonal n w]
  norm_num [Complex.mul_re]
  ring

/-- The literal incident-minus-return energy tends to the original native
boundary energy at the EULER limit, with no remaining fitted normalization. -/
theorem physical_euler_channel_balance_tendsto (n : ℕ) (x : ℕ → ℕ →₀ ℂ)
    (w : Fin (2*n) → ℂ)
    (hx : ∀ᶠ k : ℕ in atTop, (x k).support ⊆ Finset.range (2*n))
    (hv : Tendsto (fun k => physicalEulerChart n k (x k)) atTop (nhds w)) :
    Tendsto (fun k => ‖(physicalCompletedFiniteSource k (x k)).1‖^2-
      ‖(physicalCompletedFiniteSource k (x k)).2‖^2) atTop
      (nhds (nativeSourceFiniteBoundaryEnergy (2*n) w)) := by
  have he : nativeSourceFiniteBoundaryEnergy (2*n) (eulerNewton (2*n) 0 w)/2=
      nativeSourceFiniteBoundaryEnergy (2*n) w := by rw [boundary_energy_euler_zero]; ring
  simpa only [he] using physical_channel_balance_tendsto n x w hx hv

end
end CarryMovingEulerBalance
