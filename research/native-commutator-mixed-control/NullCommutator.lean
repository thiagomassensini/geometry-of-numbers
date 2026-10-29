import NativeWeightLaw

namespace CarryCommutatorControl
open CarrySelfAdjointOperator CarryNativeTfvd NativeCauchyPorts
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

theorem coefficient_outside_prefix {N : ℕ} (c : ℕ →₀ ℂ)
    (hc : c.support ⊆ Finset.range N) (j : ℕ) (hj : N ≤ j) : c j = 0 := by
  by_contra h
  have he := Finset.mem_range.mp (hc (Finsupp.mem_support_iff.mpr h))
  omega

theorem commutator_weight_scale (eta : ℝ) (a : ℂ) (w : ℕ → ℂ) (c : ℕ →₀ ℂ) :
    completionCommutator eta (fun j => a*w j) c = a • completionCommutator eta w c := by
  ext j
  cases j with
  | zero => simp [completion_commutator_zero]
  | succ j => simp only [completion_commutator_succ, Finsupp.smul_apply, smul_eq_mul]; ring

/-- The forward neighbor N is retained: the required regular prefix is N+1. -/
theorem commutator_equal_of_constant_difference {N : ℕ} (eta : ℝ)
    (a b : ℕ → ℂ) (q : ℂ) (c : ℕ →₀ ℂ)
    (hc : c.support ⊆ Finset.range N)
    (hd : ∀ j : ℕ, j < N + 1 → a j - b j = q) :
    completionCommutator eta a c = completionCommutator eta b c := by
  ext j
  cases j with
  | zero => simp [completion_commutator_zero]
  | succ j =>
    simp only [completion_commutator_succ]
    by_cases hj : j < N
    · have h0 := hd j (by omega)
      have h1 := hd (j+1) (by omega)
      by_cases hj2 : j + 2 < N
      · have h2 := hd (j+2) (by omega)
        have hback : a j - a (j+1) = b j - b (j+1) := by linear_combination h0-h1
        have hfront : a (j+2)-a (j+1) = b (j+2)-b (j+1) := by linear_combination h2-h1
        rw [hback,hfront]
      · rw [coefficient_outside_prefix c hc (j+2) (by omega)]
        have hback : a j-a (j+1) = b j-b (j+1) := by linear_combination h0-h1
        rw [hback]
        simp only [mul_zero, zero_add]
    · rw [coefficient_outside_prefix c hc j (by omega),
        coefficient_outside_prefix c hc (j+2) (by omega)]
      simp only [mul_zero, add_zero]

/-- The common physical defect is the commutator of the ORIGINAL logarithmic
response. The constant chiral carrier cancels; no amplitude is adjusted. -/
theorem native_commutator_response {N : ℕ} (eta : ℝ) (k : ℕ) (c : ℕ →₀ ℂ)
    (hc : c.support ⊆ Finset.range N)
    (hF : ∀ j : Fin (N+1), completedNativeOperatorCharacteristic
      (canonicalCompletedC3RadialTiltPoint k j) ≠ 0) :
    completionCommutator eta (incidentWeight k) c =
      (2 / (Real.sqrt 2 : ℂ)) • completionCommutator eta (responseWeight k) c := by
  have hs : (Real.sqrt 2 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hd (j : ℕ) (hj : j < N+1) :
      incidentWeight k j - (2/(Real.sqrt 2 : ℂ))*responseWeight k j =
        Complex.I/(Real.sqrt 2 : ℂ) := by
    unfold incidentWeight responseWeight
    rw [incident_amplitude_response _ (hF ⟨j,hj⟩)]
    field_simp [hs]
    ring
  rw [commutator_equal_of_constant_difference eta (incidentWeight k)
    (fun j => (2/(Real.sqrt 2 : ℂ))*responseWeight k j)
    (Complex.I/(Real.sqrt 2 : ℂ)) c hc hd, commutator_weight_scale]

/-- Both physical commutator legs coincide, before any signed pairing. -/
theorem completed_commutator_equal_legs {N : ℕ} (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (k : ℕ) (c : ℕ →₀ ℂ) (hc : c.support ⊆ Finset.range N)
    (hd : ∀ j : ℕ, j < N+1 → incidentWeight k j - returnedWeight k j = chiralDifference) :
    (completedSourceParts eta h0 h1 k c 2).1 =
      (completedSourceParts eta h0 h1 k c 2).2 := by
  have he := commutator_equal_of_constant_difference eta (incidentWeight k)
    (returnedWeight k) chiralDifference c hc hd
  change (Real.sqrt ((k : ℝ)+1) : ℂ) • NativeLaguerre.physicalGreenOperator eta h0.le h1
    (NativeLaguerre.physicalCauchySynthesis (completionCommutator eta (incidentWeight k) c)) =
    (Real.sqrt ((k : ℝ)+1) : ℂ) • NativeLaguerre.physicalGreenOperator eta h0.le h1
      (NativeLaguerre.physicalCauchySynthesis (completionCommutator eta (returnedWeight k) c))
  rw [he]

/-- This is a fully polarized zero, not merely equality of diagonal norms. -/
theorem completed_commutator_pairing_zero {N : ℕ} (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (k : ℕ) (c d : ℕ →₀ ℂ)
    (hc : c.support ⊆ Finset.range N) (hdc : d.support ⊆ Finset.range N)
    (hd : ∀ j : ℕ, j < N+1 → incidentWeight k j - returnedWeight k j = chiralDifference) :
    canonicalCompletedNativeProjectiveChiralForm
      (completedSourceParts eta h0 h1 k c 2) (completedSourceParts eta h0 h1 k d 2) = 0 := by
  unfold canonicalCompletedNativeProjectiveChiralForm
  rw [completed_commutator_equal_legs eta h0 h1 k c hc hd,
    completed_commutator_equal_legs eta h0 h1 k d hdc hd]
  ring

theorem completed_commutator_eventually_null (N : ℕ) (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    ∀ᶠ k : ℕ in atTop, ∀ c d : ℕ →₀ ℂ,
      c.support ⊆ Finset.range N → d.support ⊆ Finset.range N →
      canonicalCompletedNativeProjectiveChiralForm
        (completedSourceParts eta h0 h1 k c 2) (completedSourceParts eta h0 h1 k d 2) = 0 := by
  filter_upwards [radial_weight_difference_eventually (N+1)] with k hk
  intro c d hc hd
  exact completed_commutator_pairing_zero eta h0 h1 k c d hc hd hk

end
end CarryCommutatorControl
