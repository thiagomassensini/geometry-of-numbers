import CubicCrossings

namespace CarryGreenCubic
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryCommutatorControl CarryStencilBoundary
open CarrySpatialCorrection CarryEnergyCorrection CarryOddEnergy CarryMixedParity CarryCrossRadial CarryGreenLeading NativeLaguerre
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

/-- The weights 1/4 and 2 preserve both ordered complete vector pairings. -/
theorem sum_cubic_pairings (z : ℂ)
    (U V W X : Fin 3 → CanonicalCompletedNativeChiralCauchyCarrier) :
    (∑ a : Fin 3, ∑ b : Fin 3, z*((1/4:ℂ)*inner ℂ (U a) (V b)+2*inner ℂ (W a) (X b)))=
      z*((1/4:ℂ)*inner ℂ (∑ a : Fin 3, U a) (∑ b : Fin 3, V b)+
        2*inner ℂ (∑ a : Fin 3, W a) (∑ b : Fin 3, X b)) := by
  rw [← double_inner_sum,← double_inner_sum]
  simp only [Finset.mul_sum,Finset.sum_add_distrib,mul_add]

/-- Independent recomposition through original TFVD vectors and Cauchy Gram;
the scalar cubic theorem of PR110 is NOT used as input. -/
theorem sum_cubic_eq (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) :
    (∑ a : Fin 3, ∑ b : Fin 3, cubicCoefficient eta h0 h1 a b)=doubledNext := by
  unfold cubicCoefficient
  rw [sum_cubic_pairings]
  simp only [constantPart,cubicProfile,part_field_reconstruction]
  have hone (c : ℕ →₀ ℂ) : coefficientWeight (fun _ => 1) c=c := by
    ext j; simp [coefficient_weight_apply]
  rw [hone,hone]
  have he : nativeEvenProfile 0=Finsupp.single 0 1 := by
    rw [native_profile_zero]; simp [seedInput,triple]
  have ho := odd_profile_zero
  have hpE : coefficientWeight (monomialWeight 3) (nativeEvenProfile 0)=Finsupp.single 0 1 := by
    rw [he]
    ext j
    rcases j with _ | j <;> simp [coefficient_weight_apply,monomialWeight]
  have hpO : coefficientWeight (monomialWeight 3) (nativeOddProfile 0)=
      Finsupp.single 0 Complex.I+Finsupp.single 1 (-8*Complex.I) := by
    rw [ho]
    ext j
    rcases j with _ | _ | j <;> norm_num [coefficient_weight_apply,monomialWeight]
  rw [hpE,hpO,he,ho]
  simp only [map_add,physicalCauchySynthesis,Finsupp.linearCombination_single,
    inner_add_right,inner_smul_left,inner_smul_right,
    inner_completedNativeChiralCauchyFeature]
  norm_num [doubledNext]
  ring

/-- The same source and its original leading term, reconstructed from the
NINE independently proved cubic limits. No positivity is received. -/
theorem recomposed_cubic_tendsto (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) :
    Tendsto (fun k : ℕ => ((k:ℂ)+1)*(doubledFirstPair k-((k:ℂ)+1)*doubledLeading))
      atTop (nhds doubledNext) := by
  have hl := tendsto_finsetSum Finset.univ (fun a _ => tendsto_finsetSum Finset.univ
    (fun b _ => cubic_crossing_tendsto eta h0 h1 a b))
  rw [sum_cubic_eq] at hl
  apply hl.congr'
  filter_upwards [] with k
  rw [← part_cross_sum eta h0 h1 k,← sum_leading_eq eta h0 h1]
  simp only [Finset.mul_sum,← Finset.sum_sub_distrib]

theorem recomposed_green_cubic_tendsto (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) :
    Tendsto (fun k : ℕ => ((k:ℂ)+1)*
      (crossGreenPair eta h0 h1 k (2*k+1) (radialJetCoefficients k 0)
        (radialJetCoefficients (2*k+1) 1)-((k:ℂ)+1)*doubledLeading))
      atTop (nhds doubledNext) := by
  apply (recomposed_cubic_tendsto eta h0 h1).congr'
  filter_upwards [] with k
  rw [cross_green_eq_original]
  rfl

end
end CarryGreenCubic
