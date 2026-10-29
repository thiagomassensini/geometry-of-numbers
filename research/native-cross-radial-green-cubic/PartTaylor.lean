import RadialPartExpansion

namespace CarryGreenCubic
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryCommutatorControl
open CarrySpatialCorrection CarryEnergyCorrection CarryOddEnergy CarryMixedParity CarryCrossRadial CarryGreenLeading NativeLaguerre NativeCauchyPorts
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000

/-- Finite weight sums remain WHOLE physical vectors in every original part. -/
theorem part_field_sum_weight (eta : ℝ) (h0 : 0<eta) (h1 : eta<1)
    (S : Finset ℕ) (w : ℕ → ℕ → ℂ) (c : ℕ →₀ ℂ) (a : Fin 3) :
    partField eta h0 h1 (fun j => ∑ l ∈ S, w l j) c a=
      ∑ l ∈ S, partField eta h0 h1 (w l) c a := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have hz := part_field_scale_weight eta h0 h1 (0:ℂ) (fun _ => 1) c a
    simpa using hz
  | @insert l S hl ih =>
    simp only [Finset.sum_insert hl]
    rw [part_field_add_weight,ih]

/-- Arbitrary Taylor degree and arbitrary finite input, with the SAME native
remainder at every retained address, BEFORE any inner product or scalar readout. -/
theorem part_full_taylor_expansion (N : ℕ) (eta : ℝ) (h0 : 0<eta) (h1 : eta<1)
    (c : ℕ →₀ ℂ) : ∀ᶠ z : ℂ in nhds 0, ∀ a : Fin 3,
      partField eta h0 h1 (responseSamples z) c a=
        (∑ l ∈ Finset.range N, ((-1:ℂ)^l*(h l:ℂ)*z^(2*l+1)) •
          partField eta h0 h1 (monomialWeight (2*l+1)) c a)+
        z^(2*N+1) • partField eta h0 h1 (remainderSamples N z) c a := by
  obtain ⟨M,hM⟩ := part_field_finite_locality eta h0 h1 c
  filter_upwards [response_samples_prefix N M] with z hz
  intro a
  rw [hM (responseSamples z)
    (fun j : ℕ => taylorSamples N z j+z^(2*N+1)*remainderSamples N z j) hz a,
    part_field_add_weight,part_field_scale_weight]
  unfold taylorSamples
  rw [part_field_sum_weight]
  simp only [part_field_scale_weight]

theorem part_full_remainder_continuous (N : ℕ) (eta : ℝ) (h0 : 0<eta) (h1 : eta<1)
    (c : ℕ →₀ ℂ) (a : Fin 3) :
    ContinuousAt (fun z : ℂ => partField eta h0 h1 (remainderSamples N z) c a) 0 :=
  part_field_continuous eta h0 h1 (fun z => remainderSamples N z) c
    (CarryMixedImaginary.remainder_samples_continuous N) a

/-- Cubic ADDRESS weight of the SAME input; it is not the third jet. -/
abbrev cubicProfile (eta : ℝ) (h0 : 0<eta) (h1 : eta<1)
    (c : ℕ →₀ ℂ) (a : Fin 3) := partField eta h0 h1 (monomialWeight 3) c a

/-- Geometric compensation at EVERY address degree d for the SAME native even
input: (u,v,0) becomes (2^d u,v,(1-2^d)u). No moment enters this identity. -/
theorem seed_address_compensation (d : ℕ) (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) :
    partField eta h0 h1 (monomialWeight d) (nativeEvenProfile 0) 0=
      (2:ℂ)^d • constantPart eta h0 h1 (nativeEvenProfile 0) 0 ∧
    partField eta h0 h1 (monomialWeight d) (nativeEvenProfile 0) 1=
      constantPart eta h0 h1 (nativeEvenProfile 0) 1 ∧
    partField eta h0 h1 (monomialWeight d) (nativeEvenProfile 0) 2=
      (1-(2:ℂ)^d) • constantPart eta h0 h1 (nativeEvenProfile 0) 0 := by
  have he : nativeEvenProfile 0=Finsupp.single 0 1 := by
    rw [native_profile_zero]; simp [seedInput,triple]
  have hb : finiteTfvdBulk eta (nativeEvenProfile 0)=Finsupp.single 1 (eta:ℂ) := by
    rw [he]
    ext j
    rcases j with _ | _ | j <;> simp [finiteTfvdBulk_zero,finiteTfvdBulk_succ]
  have hone (c : ℕ →₀ ℂ) : coefficientWeight (fun _ => 1) c=c := by
    ext j; simp [coefficient_weight_apply]
  have hC : constantPart eta h0 h1 (nativeEvenProfile 0) 0=
      (eta:ℂ) • physicalGreenOperator eta h0.le h1 (completedNativeChiralCauchyFeature 1) := by
    change physicalGreenOperator eta h0.le h1
      (physicalCauchySynthesis (coefficientWeight (fun _ => 1) (finiteTfvdBulk eta (nativeEvenProfile 0))))=_
    rw [hone,hb]
    simp only [physicalCauchySynthesis,Finsupp.linearCombination_single,map_smul]
  have hp : coefficientWeight (monomialWeight d) (Finsupp.single 1 (eta:ℂ))=
      Finsupp.single 1 ((2:ℂ)^d*(eta:ℂ)) := by
    ext j
    rcases j with _ | _ | j <;> simp [coefficient_weight_apply,monomialWeight]
  have hbulk : partField eta h0 h1 (monomialWeight d) (nativeEvenProfile 0) 0=
      (2:ℂ)^d • constantPart eta h0 h1 (nativeEvenProfile 0) 0 := by
    rw [hC]
    change physicalGreenOperator eta h0.le h1
      (physicalCauchySynthesis (coefficientWeight (monomialWeight d) (finiteTfvdBulk eta (nativeEvenProfile 0))))=_
    rw [hb,hp]
    simp only [physicalCauchySynthesis,Finsupp.linearCombination_single,map_smul,smul_smul]
  have htrace : partField eta h0 h1 (monomialWeight d) (nativeEvenProfile 0) 1=
      constantPart eta h0 h1 (nativeEvenProfile 0) 1 := by
    simp [constantPart,partField,he,monomialWeight]
  have hwE : coefficientWeight (monomialWeight d) (nativeEvenProfile 0)=nativeEvenProfile 0 := by
    rw [he]
    ext j
    rcases j with _ | j <;> simp [coefficient_weight_apply,monomialWeight]
  refine ⟨hbulk,htrace,?_⟩
  have hs := part_field_reconstruction eta h0 h1 (monomialWeight d) (nativeEvenProfile 0)
  have hc := part_field_reconstruction eta h0 h1 (fun _ => 1) (nativeEvenProfile 0)
  simp only [Fin.sum_univ_three,hwE,hbulk,htrace] at hs
  simp only [Fin.sum_univ_three,hone] at hc
  change constantPart eta h0 h1 (nativeEvenProfile 0) 0+
    constantPart eta h0 h1 (nativeEvenProfile 0) 1+
    constantPart eta h0 h1 (nativeEvenProfile 0) 2=physicalCauchySynthesis (nativeEvenProfile 0) at hc
  have hz : constantPart eta h0 h1 (nativeEvenProfile 0) 2=0 :=
    part_constant_residual_zero eta h0 h1 (nativeEvenProfile 0)
  rw [hz,add_zero] at hc
  calc
    _ = ((2:ℂ)^d • constantPart eta h0 h1 (nativeEvenProfile 0) 0+
          constantPart eta h0 h1 (nativeEvenProfile 0) 1+
          partField eta h0 h1 (monomialWeight d) (nativeEvenProfile 0) 2)-
        ((2:ℂ)^d • constantPart eta h0 h1 (nativeEvenProfile 0) 0+
          constantPart eta h0 h1 (nativeEvenProfile 0) 1) := by abel
    _ = _ := by rw [hs,← hc]; module

end
end CarryGreenCubic
