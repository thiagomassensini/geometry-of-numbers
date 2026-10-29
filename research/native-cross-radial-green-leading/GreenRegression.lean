import LeadingCrossings

namespace CarryGreenLeading
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryCommutatorControl CarryStencilBoundary
open CarrySpatialCorrection CarryEnergyCorrection CarryOddEnergy CarryMixedParity CarryCrossRadial NativeLaguerre NativeCauchyPorts
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000

theorem double_inner_sum (U V : Fin 3 → CanonicalCompletedNativeChiralCauchyCarrier) :
    (∑ a : Fin 3, ∑ b : Fin 3, inner ℂ (U a) (V b))=
      inner ℂ (∑ a : Fin 3, U a) (∑ b : Fin 3, V b) := by
  simp only [inner_sum,sum_inner]
  rw [Finset.sum_comm]

theorem sum_cross_coefficients (z : ℂ)
    (U V W X : Fin 3 → CanonicalCompletedNativeChiralCauchyCarrier) :
    (∑ a : Fin 3, ∑ b : Fin 3, z*(inner ℂ (U a) (V b)+2*inner ℂ (W a) (X b)))=
      z*(inner ℂ (∑ a : Fin 3, U a) (∑ b : Fin 3, V b)+
        2*inner ℂ (∑ a : Fin 3, W a) (∑ b : Fin 3, X b)) := by
  rw [← double_inner_sum,← double_inner_sum]
  simp only [Finset.mul_sum,Finset.sum_add_distrib,mul_add]

/-- Recomposition uses the full vector TFVD identities, then the original
Cauchy Gram. It does NOT use the scalar asymptotic theorem from PR110. -/
theorem sum_leading_eq (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) :
    (∑ a : Fin 3, ∑ b : Fin 3, leadingCoefficient eta h0 h1 a b)=doubledLeading := by
  unfold leadingCoefficient
  rw [sum_cross_coefficients]
  simp only [constantPart,linearPart,part_field_reconstruction]
  have hone (c : ℕ →₀ ℂ) : coefficientWeight (fun _ => 1) c=c := by
    ext j; simp [coefficient_weight_apply]
  rw [hone,hone]
  have he : nativeEvenProfile 0=Finsupp.single 0 1 := by
    rw [native_profile_zero]; simp [seedInput,triple]
  have ho := odd_profile_zero
  have hpE : coefficientWeight (monomialWeight 1) (nativeEvenProfile 0)=Finsupp.single 0 1 := by
    rw [he]
    ext j
    rcases j with _ | j <;> simp [coefficient_weight_apply,monomialWeight]
  have hpO : coefficientWeight (monomialWeight 1) (nativeOddProfile 0)=
      Finsupp.single 0 Complex.I+Finsupp.single 1 (-2*Complex.I) := by
    rw [ho]
    ext j
    rcases j with _ | _ | j <;> simp [coefficient_weight_apply,monomialWeight]
  rw [hpE,hpO,he,ho]
  simp only [map_add,physicalCauchySynthesis,Finsupp.linearCombination_single,
    inner_add_right,inner_smul_left,inner_smul_right,
    inner_completedNativeChiralCauchyFeature]
  norm_num [doubledLeading]
  ring

/-- Exact source recomposition in all nine ordered terms, at every k. -/
theorem part_cross_sum (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) (k : ℕ) :
    (∑ a : Fin 3, ∑ b : Fin 3, partCross eta h0 h1 a b k)=doubledFirstPair k :=
  (cross_source_nine_pairings eta h0 h1 k (2*k+1)
    (radialJetCoefficients k 0) (radialJetCoefficients (2*k+1) 1)).symm

/-- The leading coefficient of the complete original source is recovered
from its NINE separately controlled physical crossings. -/
theorem recomposed_leading_tendsto (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) :
    Tendsto (fun k : ℕ => (radialStep k:ℂ)*doubledFirstPair k) atTop (nhds doubledLeading) := by
  have hl := tendsto_finsetSum Finset.univ (fun a _ => tendsto_finsetSum Finset.univ
    (fun b _ => part_cross_scaled_tendsto eta h0 h1 a b))
  rw [sum_leading_eq] at hl
  apply hl.congr'
  filter_upwards [] with k
  rw [← part_cross_sum eta h0 h1 k]
  simp only [Finset.mul_sum]

/-- Residual-residual is zero at leading order for a PROVED vector reason. -/
theorem leading_residual_residual_zero (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) :
    leadingCoefficient eta h0 h1 2 2=0 := by
  simp only [leadingCoefficient,constantPart,part_constant_residual_zero,
    inner_zero_left,inner_zero_right,mul_zero,zero_add]

/-- Residual row retains the second ordered crossing. -/
theorem leading_residual_row (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) (b : Fin 3) :
    leadingCoefficient eta h0 h1 2 b=
      2*(Real.sqrt 2:ℂ)*(h 0:ℂ)*inner ℂ
        (linearPart eta h0 h1 (nativeEvenProfile 0) 2)
        (constantPart eta h0 h1 (nativeOddProfile 0) b) := by
  simp only [leadingCoefficient,constantPart,part_constant_residual_zero,inner_zero_left,zero_add]
  ring

/-- Residual column retains the first ordered crossing. -/
theorem leading_residual_column (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) (a : Fin 3) :
    leadingCoefficient eta h0 h1 a 2=
      (Real.sqrt 2:ℂ)*(h 0:ℂ)*inner ℂ
        (constantPart eta h0 h1 (nativeEvenProfile 0) a)
        (linearPart eta h0 h1 (nativeOddProfile 0) 2) := by
  simp only [leadingCoefficient,constantPart,part_constant_residual_zero,
    inner_zero_right,mul_zero,add_zero]

/-- The variable response residual is an actual ORIGINAL Green vector. -/
theorem linear_even_residual (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) :
    linearPart eta h0 h1 (nativeEvenProfile 0) 2=
      (-(eta:ℂ)) • physicalGreenOperator eta h0.le h1 (completedNativeChiralCauchyFeature 1) := by
  have he : nativeEvenProfile 0=Finsupp.single 0 1 := by
    rw [native_profile_zero]; simp [seedInput,triple]
  change physicalGreenOperator eta h0.le h1
    (physicalCauchySynthesis (completionCommutator eta (monomialWeight 1) (nativeEvenProfile 0)))=_
  rw [he,commutator_seed]
  rw [show monomialWeight 1 0=(1:ℂ) by norm_num [monomialWeight],
    show monomialWeight 1 1=(2:ℂ) by norm_num [monomialWeight],
    show (eta:ℂ)*(1-2)= -(eta:ℂ) by ring]
  simp only [physicalCauchySynthesis,Finsupp.linearCombination_single,map_smul]

/-- Exact VECTOR compensation in the even source: (Cbulk,Ctrace,0)
becomes (2 Cbulk,Ctrace,-Cbulk) at the first address degree. -/
theorem even_vector_compensation (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) :
    linearPart eta h0 h1 (nativeEvenProfile 0) 0=
      (2:ℂ) • constantPart eta h0 h1 (nativeEvenProfile 0) 0 ∧
    linearPart eta h0 h1 (nativeEvenProfile 0) 1=
      constantPart eta h0 h1 (nativeEvenProfile 0) 1 ∧
    linearPart eta h0 h1 (nativeEvenProfile 0) 2=
      -constantPart eta h0 h1 (nativeEvenProfile 0) 0 := by
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
  have hp : coefficientWeight (monomialWeight 1) (Finsupp.single 1 (eta:ℂ))=
      Finsupp.single 1 (2*(eta:ℂ)) := by
    ext j
    rcases j with _ | _ | j <;> simp [coefficient_weight_apply,monomialWeight]
  refine ⟨?_,?_,?_⟩
  · rw [hC]
    change physicalGreenOperator eta h0.le h1
      (physicalCauchySynthesis (coefficientWeight (monomialWeight 1) (finiteTfvdBulk eta (nativeEvenProfile 0))))=_
    rw [hb,hp]
    simp only [physicalCauchySynthesis,Finsupp.linearCombination_single,map_smul,smul_smul]
  · simp [linearPart,constantPart,partField,he,monomialWeight]
  · rw [linear_even_residual,hC]
    module

/-- This nonzero vector is certified WITHOUT a canonical-moment sign. -/
theorem linear_even_residual_ne_zero (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) :
    linearPart eta h0 h1 (nativeEvenProfile 0) 2≠0 := by
  have hv : physicalGreenOperator eta h0.le h1 (completedNativeChiralCauchyFeature 1)≠0 := by
    intro hz
    have hp := green_seed_cross_re_pos eta h0 h1
    rw [hz,inner_zero_right] at hp
    norm_num at hp
  rw [linear_even_residual]
  exact smul_ne_zero (neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr h0.ne')) hv

end
end CarryGreenLeading
