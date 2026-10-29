import MixedPairing

namespace CarryCrossRadial
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryStencilBoundary
open CarrySpatialCorrection CarryEnergyCorrection CarryOddEnergy CarryMixedParity NativeLaguerre CarryCommutatorControl
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000

/-- Literal product of the two ORIGINAL radial amplitudes. -/
def crossScale (k l : ℕ) : ℝ := Real.sqrt ((k:ℝ)+1)*Real.sqrt ((l:ℝ)+1)

theorem cross_scale_symm (k l : ℕ) : crossScale k l=crossScale l k := by
  unfold crossScale; ring

theorem cross_scale_diagonal (k : ℕ) : crossScale k k=(k:ℝ)+1 := by
  unfold crossScale
  rw [← pow_two, Real.sq_sqrt (by positivity)]

theorem cross_scale_pos (k l : ℕ) : 0 < crossScale k l := by
  unfold crossScale; positivity

/-- No source, amplitude, return or metric is changed. -/
abbrev crossSignedPair (k l : ℕ) (c d : ℕ →₀ ℂ) : ℂ :=
  canonicalCompletedNativeProjectiveChiralForm
    (physicalCompletedFiniteSource k c) (physicalCompletedFiniteSource l d)

theorem cross_pair_diagonal (k : ℕ) (c d : ℕ →₀ ℂ) :
    crossSignedPair k k c d=signedPair k c d := rfl

/-- Both original scales, before pairing the two complete vector observables. -/
theorem cross_contrast_mean_scale (k l : ℕ) :
    conj ((Real.sqrt ((k:ℝ)+1):ℂ)*chiralDifference)*
      ((Real.sqrt ((l:ℝ)+1):ℂ)*(2/(Real.sqrt 2:ℂ)))=
        -2*Complex.I*(crossScale k l:ℂ) := by
  have hs : (Real.sqrt 2:ℂ)^2=2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hn : (Real.sqrt 2:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num)).ne'
  have ha : conj chiralDifference*(2/(Real.sqrt 2:ℂ))= -2*Complex.I := by
    simp only [chiralDifference, map_div₀, map_mul, map_ofNat, Complex.conj_I, Complex.conj_ofReal]
    field_simp [hn]
    linear_combination hs
  calc
    _ = (conj chiralDifference*(2/(Real.sqrt 2:ℂ)))*
        (Real.sqrt ((k:ℝ)+1):ℂ)*(Real.sqrt ((l:ℝ)+1):ℂ) := by
      simp only [map_mul, Complex.conj_ofReal]; ring
    _ = _ := by rw [ha]; unfold crossScale; push_cast; ring

/-- TWO independently regularized complete states. Both whole vector means
and contrasts are transported before the original complex signed pairing. -/
theorem complete_cross_pair {N M : ℕ} (k l : ℕ) (c d : ℕ →₀ ℂ)
    (hc : c.support ⊆ Finset.range N) (hdc : d.support ⊆ Finset.range M)
    (hFk : ∀ j : Fin N, completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k j)≠0)
    (hFl : ∀ j : Fin M, completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint l j)≠0)
    (hdk : ∀ j : ℕ, j<N → incidentWeight k j-returnedWeight k j=chiralDifference)
    (hdl : ∀ j : ℕ, j<M → incidentWeight l j-returnedWeight l j=chiralDifference) :
    crossSignedPair k l c d=(crossScale k l:ℂ)*
      (kernel (responseSamples (radialStep l)) c d+
        conj (kernel (responseSamples (radialStep k)) d c)) := by
  obtain ⟨hcd,hcm⟩ := source_mean_and_contrast k c hc hFk hdk
  obtain ⟨hdd,hdm⟩ := source_mean_and_contrast l d hdc hFl hdl
  have he := signed_mean_contrast (physicalCompletedFiniteSource k c) (physicalCompletedFiniteSource l d)
  rw [hcd, hdm, hcm, hdd] at he
  simp only [inner_smul_left, inner_smul_right] at he
  have hi : inner ℂ (physicalCauchySynthesis (coefficientWeight (responseWeight k) c))
      (physicalCauchySynthesis d)=conj (kernel (responseWeight k) d c) := by
    change inner ℂ _ _=conj (inner ℂ _ _)
    rw [inner_conj_symm]
    rfl
  rw [hi] at he
  have hkernel : inner ℂ (physicalCauchySynthesis c)
      (physicalCauchySynthesis (coefficientWeight (responseWeight l) d))=kernel (responseWeight l) c d := rfl
  rw [hkernel] at he
  have hs := cross_contrast_mean_scale k l
  have ht : conj ((Real.sqrt ((k:ℝ)+1):ℂ)*(2/(Real.sqrt 2:ℂ)))*
      ((Real.sqrt ((l:ℝ)+1):ℂ)*chiralDifference)=2*Complex.I*(crossScale k l:ℂ) := by
    have hh := congrArg conj (cross_contrast_mean_scale l k)
    norm_num [map_mul, map_div₀, map_ofNat, Complex.conj_ofReal] at hh ⊢
    rw [cross_scale_symm l k] at hh
    linear_combination hh
  have hpair : crossSignedPair k l c d=
      -Complex.I*(crossScale k l:ℂ)*kernel (responseWeight l) c d+
       Complex.I*(crossScale k l:ℂ)*conj (kernel (responseWeight k) d c) := by
    change crossSignedPair k l c d=_ at he
    linear_combination he+(1/2:ℂ)*kernel (responseWeight l) c d*hs+
      (1/2:ℂ)*conj (kernel (responseWeight k) d c)*ht
  have hw (j : ℕ) : responseWeight j=(fun a => Complex.I*responseSamples (radialStep j) a) := by
    funext a; exact response_radial_readout j a
  rw [hpair, hw l, hw k, kernel_scale, kernel_scale]
  simp only [map_mul, Complex.conj_I]
  ring_nf
  norm_num [Complex.I_sq]

/-- The same independently indexed original finite even/odd jet inputs. -/
def crossMixedPair (S T : Finset ℕ) (c d : ℕ → ℝ) (k l : ℕ) : ℂ :=
  crossSignedPair k l (finiteJetSource S c k) (finiteOddJetSource T d l)

/-- Eventual regularity is discharged independently on both actual prefixes. -/
theorem cross_mixed_exact {α : Type*} {f : Filter α} (u v : α → ℕ)
    (hu : Tendsto u f atTop) (hv : Tendsto v f atTop)
    (S T : Finset ℕ) (c d : ℕ → ℝ) :
    ∀ᶠ a in f, crossMixedPair S T c d (u a) (v a)=(crossScale (u a) (v a):ℂ)*
      (kernel (responseSamples (radialStep (v a))) (finiteJetSource S c (u a)) (finiteOddJetSource T d (v a))-
       kernel (responseSamples (radialStep (u a))) (finiteOddJetSource T d (v a)) (finiteJetSource S c (u a))) := by
  let N := 2*S.sup id+1
  let M := 2*T.sup id+2
  filter_upwards [hu.eventually (canonicalCompletedNativeRadialProjectiveChiral_eventually_regular N),
    hv.eventually (canonicalCompletedNativeRadialProjectiveChiral_eventually_regular M)] with a hk hl
  have hc := finite_source_support S c (u a)
  have hd := finite_odd_source_support T d (v a)
  have hFk (j : Fin N) := (hk j).2.1
  have hFl (j : Fin M) := (hl j).2.1
  have hdk (j : ℕ) (hj : j<N) := radial_weight_difference (u a) j (hk ⟨j,hj⟩).2.1 (hk ⟨j,hj⟩).2.2
  have hdl (j : ℕ) (hj : j<M) := radial_weight_difference (v a) j (hl ⟨j,hj⟩).2.1 (hl ⟨j,hj⟩).2.2
  have he := complete_cross_pair (u a) (v a) _ _ hc hd hFk hFl hdk hdl
  rw [kernel_imaginary_real _ _ _ (response_samples_real (radialStep (u a)))
    (odd_coefficients_imaginary T d (v a)) (even_coefficients_real S c (u a))] at he
  exact he

theorem cross_mixed_conjugate {α : Type*} {f : Filter α} (u v : α → ℕ)
    (hu : Tendsto u f atTop) (hv : Tendsto v f atTop)
    (S T : Finset ℕ) (c d : ℕ → ℝ) :
    ∀ᶠ a in f, conj (crossMixedPair S T c d (u a) (v a))=
      -crossMixedPair S T c d (u a) (v a) := by
  filter_upwards [cross_mixed_exact u v hu hv S T c d] with a ha
  rw [ha]
  simp only [map_mul, map_sub, Complex.conj_ofReal]
  rw [kernel_real_imaginary _ _ _ (response_samples_real (radialStep (v a)))
    (even_coefficients_real S c (u a)) (odd_coefficients_imaginary T d (v a)),
    kernel_imaginary_real _ _ _ (response_samples_real (radialStep (u a)))
    (odd_coefficients_imaginary T d (v a)) (even_coefficients_real S c (u a))]
  ring

theorem cross_mixed_real_zero {α : Type*} {f : Filter α} (u v : α → ℕ)
    (hu : Tendsto u f atTop) (hv : Tendsto v f atTop)
    (S T : Finset ℕ) (c d : ℕ → ℝ) :
    ∀ᶠ a in f, (crossMixedPair S T c d (u a) (v a)).re=0 := by
  filter_upwards [cross_mixed_conjugate u v hu hv S T c d] with a ha
  have he := congrArg Complex.re ha
  simp only [Complex.conj_re, Complex.neg_re] at he
  linarith

end
end CarryCrossRadial
