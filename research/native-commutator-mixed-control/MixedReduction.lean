import NullCommutator

namespace CarryCommutatorControl
open CarrySelfAdjointOperator CarryNativeTfvd
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

private theorem isotropic_left (e x : CanonicalCompletedNativeProjectiveChiralCarrier)
    (he : e.1 = e.2) :
    canonicalCompletedNativeProjectiveChiralForm e x =
      (2 : ℂ)⁻¹ * inner ℂ e.1 (x.1-x.2) := by
  unfold canonicalCompletedNativeProjectiveChiralForm
  rw [← he, inner_sub_right]

private theorem isotropic_right (x e : CanonicalCompletedNativeProjectiveChiralCarrier)
    (he : e.1 = e.2) :
    canonicalCompletedNativeProjectiveChiralForm x e =
      (2 : ℂ)⁻¹ * inner ℂ (x.1-x.2) e.1 := by
  unfold canonicalCompletedNativeProjectiveChiralForm
  rw [← he, inner_sub_left]

theorem coefficient_weight_difference {N : ℕ} (k : ℕ) (c : ℕ →₀ ℂ)
    (hc : c.support ⊆ Finset.range N)
    (hd : ∀ j : ℕ, j < N → incidentWeight k j-returnedWeight k j=chiralDifference) :
    coefficientWeight (incidentWeight k) c - coefficientWeight (returnedWeight k) c =
      chiralDifference • c := by
  ext j
  simp only [Finsupp.sub_apply, coefficient_weight_apply, Finsupp.smul_apply, smul_eq_mul]
  by_cases hj : j < N
  · rw [← sub_mul, hd j hj]
  · rw [coefficient_outside_prefix c hc j (by omega)]
    ring

/-- The whole physical source retains its original nonzero contrast vector. -/
theorem completed_source_contrast {N : ℕ} (k : ℕ) (c : ℕ →₀ ℂ)
    (hc : c.support ⊆ Finset.range N)
    (hd : ∀ j : ℕ, j < N → incidentWeight k j-returnedWeight k j=chiralDifference) :
    (NativeLaguerre.physicalCompletedFiniteSource k c).1 -
      (NativeLaguerre.physicalCompletedFiniteSource k c).2 =
      ((Real.sqrt ((k : ℝ)+1) : ℂ) * chiralDifference) •
        NativeLaguerre.physicalCauchySynthesis c := by
  rw [completed_source_weighted_identity]
  simp only [← smul_sub]
  rw [← map_sub, coefficient_weight_difference k c hc hd, map_smul, smul_smul]

/-- All mixed correction sectors combine against the SAME original source
contrast. Neither argument is scalarized or assumed to have a sign. -/
theorem completed_commutator_mixed_pairing {N : ℕ}
    (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (k : ℕ) (c d : ℕ →₀ ℂ)
    (hc : c.support ⊆ Finset.range N) (hdc : d.support ⊆ Finset.range N)
    (hd : ∀ j : ℕ, j < N+1 → incidentWeight k j-returnedWeight k j=chiralDifference) :
    canonicalCompletedNativeProjectiveChiralForm (completedSourceParts eta h0 h1 k c 2)
      (NativeLaguerre.physicalCompletedFiniteSource k d) +
    canonicalCompletedNativeProjectiveChiralForm (NativeLaguerre.physicalCompletedFiniteSource k c)
      (completedSourceParts eta h0 h1 k d 2) =
    (2 : ℂ)⁻¹ *
      (inner ℂ (completedSourceParts eta h0 h1 k c 2).1
        (((Real.sqrt ((k : ℝ)+1) : ℂ) * chiralDifference) • NativeLaguerre.physicalCauchySynthesis d) +
       inner ℂ (((Real.sqrt ((k : ℝ)+1) : ℂ) * chiralDifference) • NativeLaguerre.physicalCauchySynthesis c)
        (completedSourceParts eta h0 h1 k d 2).1) := by
  rw [isotropic_left _ _ (completed_commutator_equal_legs eta h0 h1 k c hc hd),
    isotropic_right _ _ (completed_commutator_equal_legs eta h0 h1 k d hdc hd),
    completed_source_contrast k d hdc (fun j hj => hd j (by omega)),
    completed_source_contrast k c hc (fun j hj => hd j (by omega))]
  ring

private theorem split_isotropic_correction
    (x e y f : CanonicalCompletedNativeProjectiveChiralCarrier)
    (he : canonicalCompletedNativeProjectiveChiralForm e f=0) :
    canonicalCompletedNativeProjectiveChiralForm (x+e) (y+f) =
      canonicalCompletedNativeProjectiveChiralForm x y +
      canonicalCompletedNativeProjectiveChiralForm e (y+f) +
      canonicalCompletedNativeProjectiveChiralForm (x+e) f := by
  unfold canonicalCompletedNativeProjectiveChiralForm at *
  simp only [Prod.fst_add, Prod.snd_add, inner_add_left, inner_add_right] at *
  linear_combination -he

/-- Exact reduction of all nine original sectors to the Green/boundary
kernel plus the two complete mixed source pairings. -/
theorem completed_kernel_mixed_reduction {N : ℕ}
    (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (k : ℕ) (c d : ℕ →₀ ℂ)
    (hc : c.support ⊆ Finset.range N) (hdc : d.support ⊆ Finset.range N)
    (hd : ∀ j : ℕ, j < N+1 → incidentWeight k j-returnedWeight k j=chiralDifference) :
    canonicalCompletedNativeProjectiveChiralForm
      (NativeLaguerre.physicalCompletedFiniteSource k c) (NativeLaguerre.physicalCompletedFiniteSource k d) =
    canonicalCompletedNativeProjectiveChiralForm
      (completedSourceParts eta h0 h1 k c 0 + completedSourceParts eta h0 h1 k c 1)
      (completedSourceParts eta h0 h1 k d 0 + completedSourceParts eta h0 h1 k d 1) +
    (2 : ℂ)⁻¹ *
      (inner ℂ (completedSourceParts eta h0 h1 k c 2).1
        (((Real.sqrt ((k : ℝ)+1) : ℂ) * chiralDifference) • NativeLaguerre.physicalCauchySynthesis d) +
       inner ℂ (((Real.sqrt ((k : ℝ)+1) : ℂ) * chiralDifference) • NativeLaguerre.physicalCauchySynthesis c)
        (completedSourceParts eta h0 h1 k d 2).1) := by
  have ht := split_isotropic_correction
    (completedSourceParts eta h0 h1 k c 0 + completedSourceParts eta h0 h1 k c 1)
    (completedSourceParts eta h0 h1 k c 2)
    (completedSourceParts eta h0 h1 k d 0 + completedSourceParts eta h0 h1 k d 1)
    (completedSourceParts eta h0 h1 k d 2)
    (completed_commutator_pairing_zero eta h0 h1 k c d hc hdc hd)
  rw [← completed_source_three_parts eta h0 h1 k c,
    ← completed_source_three_parts eta h0 h1 k d] at ht
  rw [add_assoc, completed_commutator_mixed_pairing eta h0 h1 k c d hc hdc hd] at ht
  exact ht

end
end CarryCommutatorControl
