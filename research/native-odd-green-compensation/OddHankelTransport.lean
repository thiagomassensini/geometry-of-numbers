import OddCompensation

namespace CarryOddGreen
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryCommutatorControl CarryStencilBoundary
open CarrySpatialCorrection CarryEnergyCorrection CarryOddEnergy CarryMixedParity CarryCrossRadial CarryGreenLeading CarryGreenCubic NativeLaguerre
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000

/-- Odd phases in BOTH independent inputs: the real weighted Cauchy kernel
is real, without assuming its symmetry or positivity. -/
theorem kernel_imaginary_imaginary (w : ℕ → ℂ) (c d : ℕ →₀ ℂ)
    (hw : ∀ j, conj (w j)=w j) (hc : ∀ j, conj (c j)= -c j)
    (hd : ∀ j, conj (d j)= -d j) : conj (kernel w c d)=kernel w c d := by
  rw [kernel_double_sum]
  simp only [map_sum,map_div₀,map_mul,map_add,map_natCast,map_ofNat]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [hw,hc,hd,map_neg,neg_neg]
  ring

/-- Two independent ORIGINAL finite odd jet sources. This is the native
SIGNED form, not a new positive Gram or a sequence chosen from moments. -/
def oddPairing (S T : Finset ℕ) (c d : ℕ → ℝ) (k : ℕ) : ℂ :=
  signedPair k (finiteOddJetSource S c k) (finiteOddJetSource T d k)

theorem odd_ordered_kernel_sum (S T : Finset ℕ) (c d : ℕ → ℝ) (k : ℕ) :
    ((k:ℂ)+1)*
      (kernel (responseSamples (radialStep k)) (finiteOddJetSource S c k) (finiteOddJetSource T d k)+
       kernel (responseSamples (radialStep k)) (finiteOddJetSource T d k) (finiteOddJetSource S c k))=
      ∑ r ∈ S, ∑ s ∈ T, (c r:ℂ)*(d s:ℂ)*normalizedOddPair r s k := by
  rw [finite_odd_source_profile,finite_odd_source_profile,kernel_sum_inputs,kernel_sum_inputs]
  rw [Finset.sum_comm (s:=T) (t:=S)]
  simp only [kernel_scale_inputs,map_mul,map_pow,map_add,map_one,map_natCast,Complex.conj_ofReal]
  rw [← Finset.sum_add_distrib]
  simp only [← Finset.sum_add_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  unfold normalizedOddPair oddPairKernel
  rw [show 2*(r+s+1)+1=(2*r+1)+(2*s+1)+1 by omega,pow_succ,pow_add]
  ring

/-- Polarized transport with two independently chosen finite supports. The
regular prefix includes the outgoing halo; no sign hypothesis is used. -/
theorem odd_pairing_exact (S T : Finset ℕ) (c d : ℕ → ℝ) :
    ∀ᶠ k : ℕ in atTop, oddPairing S T c d k=
      ∑ r ∈ S, ∑ s ∈ T, (c r:ℂ)*(d s:ℂ)*normalizedOddPair r s k := by
  let N := (2*S.sup id+2)+(2*T.sup id+2)+1
  filter_upwards [canonicalCompletedNativeRadialProjectiveChiral_eventually_regular N] with k hk
  have hc : (finiteOddJetSource S c k).support ⊆ Finset.range N :=
    (finite_odd_source_support S c k).trans (Finset.range_mono (by dsimp [N]; omega))
  have hd : (finiteOddJetSource T d k).support ⊆ Finset.range N :=
    (finite_odd_source_support T d k).trans (Finset.range_mono (by dsimp [N]; omega))
  have hF (j : Fin N) := (hk j).2.1
  have hdiff (j : ℕ) (hj : j<N) := radial_weight_difference k j (hk ⟨j,hj⟩).2.1 (hk ⟨j,hj⟩).2.2
  have he := complete_complex_pair k _ _ hc hd hF hdiff
  rw [kernel_imaginary_imaginary _ _ _ (response_samples_real (radialStep k))
    (odd_coefficients_imaginary T d k) (odd_coefficients_imaginary S c k)] at he
  exact he.trans (odd_ordered_kernel_sum S T c d k)

/-- The preexisting exact odd expansion gives its leading moment, with
all ordered crossings and the analytic tail still present. -/
theorem normalized_odd_pair_tendsto (r s : ℕ) :
    Tendsto (normalizedOddPair r s) atTop (nhds (h (r+s+1):ℂ)) := by
  have ht : Tendsto (fun k : ℕ => (radialStep k:ℂ)) atTop (nhds 0) := by
    simpa only [Function.comp_def,Complex.ofReal_zero] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp radial_step_tendsto
  have hR := (odd_pair_remainder_continuous r s).tendsto.comp ht
  have hsmall := (((ht.pow 2).mul_const (spatialCorrection (2*r+1) (2*s+1))).mul_const (h (r+s+2):ℂ))
  have hl := ((tendsto_const_nhds (x:=(h (r+s+1):ℂ))).sub hsmall).add ((ht.pow 4).mul hR)
  simp only [zero_pow (by decide : 2≠0),zero_pow (by decide : 4≠0),zero_mul,sub_zero,add_zero] at hl
  apply hl.congr'
  filter_upwards [normalized_odd_pair_expansion r s] with k hk
  exact hk.symm

/-- Literal polarized form of the original shifted moment sequence. -/
def oddBilinear (S T : Finset ℕ) (c d : ℕ → ℝ) : ℝ :=
  ∑ r ∈ S, ∑ s ∈ T, c r*d s*h (r+s+1)

/-- All finite orders, two independent inputs, and the SAME signed source. -/
theorem odd_pairing_tendsto (S T : Finset ℕ) (c d : ℕ → ℝ) :
    Tendsto (oddPairing S T c d) atTop (nhds (oddBilinear S T c d:ℂ)) := by
  have hl := tendsto_finsetSum S (fun r _ => tendsto_finsetSum T (fun s _ =>
    (tendsto_const_nhds (x:=(c r:ℂ)*(d s:ℂ))).mul (normalized_odd_pair_tendsto r s)))
  have he : (∑ r ∈ S, ∑ s ∈ T, (c r:ℂ)*(d s:ℂ)*(h (r+s+1):ℂ))=(oddBilinear S T c d:ℂ) := by
    unfold oddBilinear
    push_cast
    rfl
  rw [he] at hl
  apply hl.congr'
  filter_upwards [odd_pairing_exact S T c d] with k hk
  exact hk.symm

/-- All NINE Green/boundary/commutator crosses, with the two original odd
inputs independently chosen and both quadratures preserved until the limit. -/
theorem odd_green_pairing_tendsto (eta : ℝ) (h0 : 0<eta) (h1 : eta<1)
    (S T : Finset ℕ) (c d : ℕ → ℝ) :
    Tendsto (fun k : ℕ => crossGreenPair eta h0 h1 k k
      (finiteOddJetSource S c k) (finiteOddJetSource T d k)) atTop
      (nhds (oddBilinear S T c d:ℂ)) := by
  apply (odd_pairing_tendsto S T c d).congr'
  filter_upwards [] with k
  rw [cross_green_eq_original]
  rfl

end
end CarryOddGreen
