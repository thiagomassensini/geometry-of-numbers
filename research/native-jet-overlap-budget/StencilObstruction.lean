import JetBudget

/-! Strict information retained by every nonzero old difference stencil.
This concerns the overlap kernel, not the sign of the full completed budget. -/
namespace CarryJetOverlap
open CarrySelfAdjointOperator CarryFiberTransport ChiralReturn
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false

theorem observedSynthesis_eq_zero_iff (k : ℕ) {N : ℕ} (c : Fin N → ℂ) :
    observedSynthesis k c=0 ↔ c=0 := by
  constructor
  · intro hc
    let d : Fin N → ℂ := fun i => c i*(Real.sqrt (2*((i : ℝ)+1)) : ℂ)
    have he : radialIncidentSynthesis 0 N d=observedSynthesis k c := by
      change (∑ i, d i • radialField 0 i)=_
      unfold observedSynthesis
      apply Finset.sum_congr rfl
      intro i _
      rw [observedCauchy_eq,smul_smul]
      simp [d,radialField,completedNativeRadialChiralCauchyState]
    have hz : d=0 := (radialIncidentSynthesis_injective 0 N) (by
      rw [he,hc,map_zero])
    funext i
    have hi : c i*(Real.sqrt (2*((i : ℝ)+1)) : ℂ)=0 := congrFun hz i
    exact (mul_eq_zero.mp hi).resolve_right (by
      exact_mod_cast (Real.sqrt_pos.mpr (by positivity : 0 < 2*((i : ℝ)+1))).ne')
  · rintro rfl
    simp [observedSynthesis]

theorem complement_zero_sum_strict (k : ℕ) {N : ℕ} (c : Fin N → ℂ)
    (hc : ∑ i, c i=0) (hne : c ≠ 0) :
    (∑ i, ∑ j, conj (c i)*c j*(1-radialOverlap k i j)).re < 0 := by
  rw [complement_zero_sum k c hc]
  have hn : observedSynthesis k c ≠ 0 := by
    intro hz
    exact hne ((observedSynthesis_eq_zero_iff k c).mp hz)
  exact neg_neg_of_pos (sq_pos_of_pos (norm_pos_iff.mpr hn))

/-- Literal binomial coefficients, with no moment-dependent adjustment. -/
def forwardStencil (order : ℕ) : Fin (order+1) → ℂ :=
  fun i => completedGreenForwardWeight order i.val

theorem forwardStencil_sum_zero {order : ℕ} (horder : 0 < order) :
    ∑ i, forwardStencil order i=0 := by
  have h := completedGreenForwardWeightPower_eq_zero_of_lt horder
  unfold completedGreenForwardWeightPower at h
  simp only [pow_zero,mul_one] at h
  unfold forwardStencil
  rw [Fin.sum_univ_eq_sum_range]
  exact h

theorem forwardStencil_ne_zero (order : ℕ) : forwardStencil order ≠ 0 := by
  intro h
  have hv := congrFun h (⟨order,by omega⟩ : Fin (order+1))
  simp [forwardStencil,completedGreenForwardWeight] at hv

/-- In EVERY positive difference order, the overlap correction is nonzero
and negative on the raw stencil. Source/Gamma weights must still be retained
when using the full budget; this theorem does not give their final sign. -/
theorem forwardStencil_complement_strict (k order : ℕ) (horder : 0 < order) :
    (∑ i : Fin (order+1), ∑ j : Fin (order+1),
      conj (forwardStencil order i)*forwardStencil order j*(1-radialOverlap k i j)).re < 0 :=
  complement_zero_sum_strict k (forwardStencil order)
    (forwardStencil_sum_zero horder) (forwardStencil_ne_zero order)

end
end CarryJetOverlap
