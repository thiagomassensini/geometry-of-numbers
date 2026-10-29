import GreenIntertwiner

namespace CarryRadialGreen
open CarryPhysicalTrace CarryRadialRefinement CarrySelfAdjointOperator
open CarrySelfAdjointOperator.NativeLaguerre CarrySelfAdjointOperator.NativeCauchyPorts
open scoped BigOperators ComplexConjugate InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem advance_embedding_shift (c : ℕ →₀ ℂ) :
    nativeAdvance (physicalCauchyEmbedding c) = physicalCauchyEmbedding (coefficientShift c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add,hc,hd]
  | single j a =>
    have hs : coefficientShift (Finsupp.single j a) = Finsupp.single (j+1) a := by
      simp [coefficientShift]
    rw [hs,physical_embedding_single,physical_embedding_single,map_smul,native_advance_feature]

/-- A bounded resolvent on the old H does NOT preserve the finite readout core,
already on its first literal column. This is an actual domain obstruction. -/
theorem resolvent_first_column_not_finite (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1) :
    ¬ ∃ c : ℕ →₀ ℂ, physicalCauchyEmbedding c = greenResolvent 1 η (physicalCauchyFeature 0) := by
  rintro ⟨c,hc⟩
  have he : c-(η : ℂ) • coefficientShift c = Finsupp.single 0 1 := by
    apply physical_embedding_injective
    rw [map_sub,map_smul,← advance_embedding_shift]
    change greenDenominator 1 η (physicalCauchyEmbedding c) = physicalCauchyFeature 0
    rw [hc,green_denominator_resolvent 1 η hη0.le hη1]
  have hz : c 0 = 1 := by
    have h := congrArg (fun f : ℕ →₀ ℂ => f 0) he
    simpa [coefficientShift_zero] using h
  have hr (n : ℕ) : c (n+1) = (η : ℂ)*c n := by
    have h := congrArg (fun f : ℕ →₀ ℂ => f (n+1)) he
    simp only [Finsupp.sub_apply,Finsupp.smul_apply,smul_eq_mul,coefficientShift_succ,
      Finsupp.single_eq_of_ne (Nat.succ_ne_zero n)] at h
    exact sub_eq_zero.mp h
  have hn (n : ℕ) : c n ≠ 0 := by
    induction n with
    | zero => rw [hz]; exact one_ne_zero
    | succ n ih =>
      rw [hr]
      exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hη0.ne') ih
  obtain ⟨N,hN⟩ := Finset.exists_nat_subset_range c.support
  have hm : N ∈ c.support := Finsupp.mem_support_iff.mpr (hn N)
  exact (Nat.lt_irrefl N) (Finset.mem_range.mp (hN hm))

end
end CarryRadialGreen
