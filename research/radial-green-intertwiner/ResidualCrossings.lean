import CanonicalGreenSectors

namespace CarryRadialGreen
open CarryPhysicalTrace CarryRadialRefinement CarrySelfAdjointOperator
open CarrySelfAdjointOperator.NativeLaguerre CarrySelfAdjointOperator.NativeCauchyPorts
open Filter Topology
open scoped BigOperators ComplexConjugate InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- Only the original finite nonvanishing requirements; NOT a sign hypothesis. -/
def sourceRegular (k : ℕ) (x : ℕ →₀ ℂ) : Prop :=
  ∀ j ∈ x.support, ∀ i ∈ ({j,j+1} : Finset ℕ),
    completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k i) ≠ 0 ∧
    completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k i) ≠ 0

def numeratorRegular (η : ℝ) (k : ℕ) (x : ℕ →₀ ℂ) : Prop :=
  sourceRegular k (finiteTfvdBulk η x) ∧ sourceRegular k x ∧ sourceRegular k (coefficientShift x)

/-- REUSE of the pre-existing equal-leg theorem, with original vectors. -/
theorem completed_residual_equal_legs (k : ℕ) (x : ℕ →₀ ℂ) (hreg : sourceRegular k x) :
    (completedResidual k x).1=(completedResidual k x).2 := by
  apply Subtype.ext
  have h := regular_finiteResidual_equal_legs k x hreg
  change (physicalCompletedFiniteResidual k x).1=(physicalCompletedFiniteResidual k x).2 at h
  rw [← completed_residual_original] at h
  exact h

theorem residual_numerator_equal_legs (η : ℝ) (k : ℕ) (x : ℕ →₀ ℂ)
    (hreg : numeratorRegular η k x) : (residualNumerator η k x).1=(residualNumerator η k x).2 := by
  have h1 := completed_residual_equal_legs k (finiteTfvdBulk η x) hreg.1
  have h2 := completed_residual_equal_legs k x hreg.2.1
  have h3 := completed_residual_equal_legs k (coefficientShift x) hreg.2.2
  change (completedResidual k (finiteTfvdBulk η x)).1+(2 : ℂ) • (completedResidual k x).1-
      (η : ℂ) • (nativeAdvance (completedResidual k x).1+(completedResidual k (coefficientShift x)).1) =
    (completedResidual k (finiteTfvdBulk η x)).2+(2 : ℂ) • (completedResidual k x).2-
      (η : ℂ) • (nativeAdvance (completedResidual k x).2+(completedResidual k (coefficientShift x)).2)
  rw [h1,h2,h3]

theorem reconstructed_residual_equal_legs (m : ℕ) (η : ℝ) (k : ℕ) (x : ℕ →₀ ℂ)
    (hreg : numeratorRegular η k x) :
    (reconstructedResidual m η k x).1=(reconstructedResidual m η k x).2 := by
  change (η : ℂ) • greenResolvent (m+1) η
      (greenResolvent (m+1) η (powerIsometry m (residualNumerator η k x).1)) =
    (η : ℂ) • greenResolvent (m+1) η
      (greenResolvent (m+1) η (powerIsometry m (residualNumerator η k x).2))
  rw [residual_numerator_equal_legs η k x hreg]

/-- Independent radial grades AND independent refinements; this whole sector
is exactly zero, not a discarded tail or a zero-vector assertion. -/
theorem reconstructed_residual_pairing_zero (m n : ℕ) (η : ℝ) (k l : ℕ) (x y : ℕ →₀ ℂ)
    (hx : numeratorRegular η k x) (hy : numeratorRegular η l y) :
    physicalForm (reconstructedResidual m η k x) (reconstructedResidual n η l y)=0 := by
  rw [physicalForm,reconstructed_residual_equal_legs m η k x hx,
    reconstructed_residual_equal_legs n η l y hy,sub_self,mul_zero]

theorem source_regular_eventually (x : ℕ →₀ ℂ) : ∀ᶠ k : ℕ in atTop, sourceRegular k x := by
  obtain ⟨N,hN⟩ := Finset.exists_nat_subset_range x.support
  filter_upwards [canonicalCompletedNativeRadialProjectiveChiral_eventually_regular (N+1)] with k hk
  intro j hj i hi
  have hjN : j<N := Finset.mem_range.mp (hN hj)
  have hiN : i<N+1 := by simp only [Finset.mem_insert,Finset.mem_singleton] at hi; omega
  exact (hk ⟨i,hiN⟩).2

theorem numerator_regular_eventually (η : ℝ) (x : ℕ →₀ ℂ) :
    ∀ᶠ k : ℕ in atTop, numeratorRegular η k x :=
  (source_regular_eventually (finiteTfvdBulk η x)).and
    ((source_regular_eventually x).and (source_regular_eventually (coefficientShift x)))

/-- No global regularity premise: each fixed finite original input is regular
eventually in each index, before the independent refinement is chosen. -/
theorem residual_pairing_eventually_zero (η : ℝ) (x y : ℕ →₀ ℂ) :
    ∀ᶠ steps : ℕ × ℕ in atTop, ∀ m n : ℕ,
      physicalForm (reconstructedResidual m η steps.1 x)
        (reconstructedResidual n η steps.2 y)=0 := by
  have hf : Tendsto (Prod.fst : ℕ × ℕ → ℕ) atTop atTop := by
    rw [← prod_atTop_atTop_eq]; exact tendsto_fst
  have hs : Tendsto (Prod.snd : ℕ × ℕ → ℕ) atTop atTop := by
    rw [← prod_atTop_atTop_eq]; exact tendsto_snd
  filter_upwards [hf.eventually (numerator_regular_eventually η x),
    hs.eventually (numerator_regular_eventually η y)] with steps hx hy
  intro m n
  exact reconstructed_residual_pairing_zero m n η _ _ x y hx hy

/-- Exact canonical source kernel: only RR vanishes. The two mixed crossings
remain, with their original coefficients and signs. -/
theorem corrected_green_three_sectors (η : ℝ) (k l i j : ℕ)
    (hi : numeratorRegular η k (Finsupp.single i 1))
    (hj : numeratorRegular η l (Finsupp.single j 1)) :
    correctedGreenPairing η k l i j =
      physicalForm (reconstructedBulk l η k (Finsupp.single i 1))
        (reconstructedBulk k η l (Finsupp.single j 1))+
      physicalForm (reconstructedBulk l η k (Finsupp.single i 1))
        (reconstructedResidual k η l (Finsupp.single j 1))+
      physicalForm (reconstructedResidual l η k (Finsupp.single i 1))
        (reconstructedBulk k η l (Finsupp.single j 1)) := by
  rw [correctedGreenPairing,reconstructed_residual_pairing_zero l k η k l _ _ hi hj,add_zero]

theorem refined_source_green_split (m : ℕ) (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1)
    (k : ℕ) (x : ℕ →₀ ℂ) : pairPower m (completedSource k x) =
      reconstructedBulk m η k x+reconstructedResidual m η k x := by
  rw [refined_completed_reconstruct m η hη0 hη1 k x]
  simp only [map_add,smul_add,reconstructedBulk,reconstructedResidual]

theorem physical_form_re_symm (u v : PhysicalPair) : (physicalForm u v).re=(physicalForm v u).re := by
  have h1 := inner_re_symm (𝕜 := ℂ) (u.1 : CanonicalCompletedNativeChiralCauchyCarrier) (v.1 : CanonicalCompletedNativeChiralCauchyCarrier)
  have h2 := inner_re_symm (𝕜 := ℂ) (u.2 : CanonicalCompletedNativeChiralCauchyCarrier) (v.2 : CanonicalCompletedNativeChiralCauchyCarrier)
  norm_num [physicalForm,Complex.mul_re,Complex.inv_re,Complex.inv_im]
  exact congrArg₂ (fun a b : ℝ => a-b) h1 h2

/-- The remaining SOURCE sign is exactly bulk balance plus the mixed crossing.
No positivity of either summand is asserted, and the residual vector is retained. -/
theorem signed_energy_bulk_plus_mixed (m : ℕ) (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1)
    (k : ℕ) (x : ℕ →₀ ℂ) (hreg : numeratorRegular η k x) :
    (physicalForm (pairPower m (completedSource k x)) (pairPower m (completedSource k x))).re =
      (physicalForm (reconstructedBulk m η k x) (reconstructedBulk m η k x)).re+
      2*(physicalForm (reconstructedBulk m η k x) (reconstructedResidual m η k x)).re := by
  rw [refined_source_green_split m η hη0 hη1 k x,physical_form_four_sectors,
    reconstructed_residual_pairing_zero m m η k k x x hreg hreg]
  simp only [Complex.add_re,add_zero]
  rw [physical_form_re_symm (reconstructedResidual m η k x) (reconstructedBulk m η k x)]
  ring

end
end CarryRadialGreen
