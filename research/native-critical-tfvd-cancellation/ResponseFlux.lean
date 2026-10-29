import NativeJets
import GreenSeed

namespace CarryCriticalTfvd
open CarrySelfAdjointOperator CarryNativeTfvd CarryCommutatorControl NativeLaguerre
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def mixedEnergy (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (k : ℕ) (c : ℕ →₀ ℂ) : ℝ :=
  (canonicalCompletedNativeProjectiveChiralForm (completedSourceParts eta h0 h1 k c 2)
      (physicalCompletedFiniteSource k c) +
   canonicalCompletedNativeProjectiveChiralForm (physicalCompletedFiniteSource k c)
      (completedSourceParts eta h0 h1 k c 2)).re

def fullEnergy (k : ℕ) (c : ℕ →₀ ℂ) : ℝ :=
  (canonicalCompletedNativeProjectiveChiralForm
    (physicalCompletedFiniteSource k c) (physicalCompletedFiniteSource k c)).re

def bulkBoundaryEnergy (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (k : ℕ) (c : ℕ →₀ ℂ) : ℝ :=
  (canonicalCompletedNativeProjectiveChiralForm
    (completedSourceParts eta h0 h1 k c 0 + completedSourceParts eta h0 h1 k c 1)
    (completedSourceParts eta h0 h1 k c 0 + completedSourceParts eta h0 h1 k c 1)).re

theorem full_split {N : ℕ} (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (k : ℕ) (c : ℕ →₀ ℂ) (hc : c.support ⊆ Finset.range N)
    (hd : ∀ j : ℕ, j < N+1 → incidentWeight k j-returnedWeight k j=chiralDifference) :
    fullEnergy k c = bulkBoundaryEnergy eta h0 h1 k c + mixedEnergy eta h0 h1 k c := by
  unfold fullEnergy bulkBoundaryEnergy mixedEnergy
  rw [completed_commutator_mixed_pairing eta h0 h1 k c c hc hc hd]
  exact congrArg Complex.re (completed_kernel_mixed_reduction eta h0 h1 k c c hc hc hd)

theorem commutator_response_field {N : ℕ} (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (k : ℕ) (c : ℕ →₀ ℂ) (hc : c.support ⊆ Finset.range N)
    (hF : ∀ j : Fin (N+1), completedNativeOperatorCharacteristic
      (canonicalCompletedC3RadialTiltPoint k j) ≠ 0) :
    (completedSourceParts eta h0 h1 k c 2).1 =
      ((Real.sqrt ((k : ℝ)+1) : ℂ)*(2/(Real.sqrt 2 : ℂ))) •
        physicalGreenOperator eta h0.le h1
          (physicalCauchySynthesis (completionCommutator eta (responseWeight k) c)) := by
  change (Real.sqrt ((k : ℝ)+1) : ℂ) • physicalGreenOperator eta h0.le h1
    (physicalCauchySynthesis (completionCommutator eta (incidentWeight k) c)) = _
  rw [native_commutator_response eta k c hc hF, map_smul, map_smul, smul_smul]

private theorem symmetric_real_inner (u v : CanonicalCompletedNativeChiralCauchyCarrier) :
    ((2 : ℂ)⁻¹ * (inner ℂ v u+inner ℂ u v)).re = (inner ℂ u v).re := by
  have h : (inner ℂ v u).re=(inner ℂ u v).re := by exact_mod_cast inner_re_symm (𝕜 := ℂ) v u
  norm_num [Complex.mul_re, Complex.add_re, h]
  ring

private theorem source_scale_product (k : ℕ) :
    conj ((Real.sqrt ((k : ℝ)+1) : ℂ)*chiralDifference) *
      ((Real.sqrt ((k : ℝ)+1) : ℂ)*(2/(Real.sqrt 2 : ℂ))) =
      -2*Complex.I*((k : ℝ)+1 : ℂ) := by
  have hs : (Real.sqrt 2 : ℂ)^2=2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hk : (Real.sqrt ((k : ℝ)+1) : ℂ)^2=((k : ℝ)+1 : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]; push_cast; rfl
  have hn : (Real.sqrt 2 : ℂ)≠0 := Complex.ofReal_ne_zero.mpr
    (Real.sqrt_pos.mpr (by norm_num)).ne'
  have ha : conj chiralDifference*(2/(Real.sqrt 2 : ℂ)) = -2*Complex.I := by
    simp only [chiralDifference,map_div₀,map_mul,map_ofNat,Complex.conj_I,Complex.conj_ofReal]
    field_simp [hn]
    linear_combination hs
  calc
    _ = (conj chiralDifference*(2/(Real.sqrt 2 : ℂ))) *
        (Real.sqrt ((k : ℝ)+1) : ℂ)^2 := by
      simp only [map_mul,Complex.conj_ofReal]
      ring
    _ = _ := by rw [ha,hk]

/-- The complete mixed correction is the flux of the ORIGINAL response
commutator. Both ordered mixed sectors precede this real readout. -/
theorem mixed_response_flux {N : ℕ} (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (k : ℕ) (c : ℕ →₀ ℂ) (hc : c.support ⊆ Finset.range N)
    (hF : ∀ j : Fin (N+1), completedNativeOperatorCharacteristic
      (canonicalCompletedC3RadialTiltPoint k j) ≠ 0)
    (hd : ∀ j : ℕ, j < N+1 → incidentWeight k j-returnedWeight k j=chiralDifference) :
    mixedEnergy eta h0 h1 k c = 2*((k : ℝ)+1) *
      (inner ℂ (physicalCauchySynthesis c)
        (physicalGreenOperator eta h0.le h1
          (physicalCauchySynthesis (completionCommutator eta (responseWeight k) c)))).im := by
  unfold mixedEnergy
  rw [completed_commutator_mixed_pairing eta h0 h1 k c c hc hc hd,
    symmetric_real_inner, commutator_response_field eta h0 h1 k c hc hF,
    inner_smul_left, inner_smul_right, ← mul_assoc, source_scale_product]
  simp [Complex.mul_re, Complex.mul_im]

theorem incident_response_coefficients {N : ℕ} (k : ℕ) (c : ℕ →₀ ℂ)
    (hc : c.support ⊆ Finset.range N)
    (hF : ∀ j : Fin N, completedNativeOperatorCharacteristic
      (canonicalCompletedC3RadialTiltPoint k j) ≠ 0) :
    coefficientWeight (incidentWeight k) c =
      (2/(Real.sqrt 2 : ℂ)) • coefficientWeight (responseWeight k) c +
      (Complex.I/(Real.sqrt 2 : ℂ)) • c := by
  ext j
  simp only [coefficient_weight_apply,Finsupp.add_apply,Finsupp.smul_apply,smul_eq_mul]
  by_cases hj : j < N
  · unfold incidentWeight responseWeight
    rw [incident_amplitude_response _ (hF ⟨j,hj⟩)]
    ring
  · rw [coefficient_outside_prefix c hc j (by omega)]
    ring

theorem source_mean_response {N : ℕ} (k : ℕ) (c : ℕ →₀ ℂ)
    (hc : c.support ⊆ Finset.range N)
    (hF : ∀ j : Fin N, completedNativeOperatorCharacteristic
      (canonicalCompletedC3RadialTiltPoint k j) ≠ 0)
    (hd : ∀ j : ℕ, j < N → incidentWeight k j-returnedWeight k j=chiralDifference) :
    (2 : ℂ)⁻¹ • ((physicalCompletedFiniteSource k c).1+(physicalCompletedFiniteSource k c).2) =
      ((Real.sqrt ((k : ℝ)+1) : ℂ)*(2/(Real.sqrt 2 : ℂ))) •
        physicalCauchySynthesis (coefficientWeight (responseWeight k) c) := by
  have hdiff := coefficient_weight_difference k c hc hd
  have hA := incident_response_coefficients k c hc hF
  have hB : coefficientWeight (returnedWeight k) c =
      (2/(Real.sqrt 2 : ℂ)) • coefficientWeight (responseWeight k) c -
      (Complex.I/(Real.sqrt 2 : ℂ)) • c := by
    rw [hA] at hdiff
    have hz : chiralDifference=2*(Complex.I/(Real.sqrt 2 : ℂ)) := by
      unfold chiralDifference; ring
    rw [hz] at hdiff
    ext j
    have hj := congrArg (fun f : ℕ →₀ ℂ => f j) hdiff
    simp only [Finsupp.sub_apply,Finsupp.add_apply,Finsupp.smul_apply,smul_eq_mul] at hj ⊢
    linear_combination -hj
  rw [completed_source_weighted_identity]
  simp only [hA,hB,map_add,map_sub,map_smul,smul_add,smul_sub,smul_smul]
  module

private theorem signed_energy_mean (p : CanonicalCompletedNativeProjectiveChiralCarrier) :
    (canonicalCompletedNativeProjectiveChiralForm p p).re =
      (inner ℂ (p.1-p.2) ((2 : ℂ)⁻¹ • (p.1+p.2))).re := by
  have hc : (inner ℂ p.1 p.2).re=(inner ℂ p.2 p.1).re := by
    exact_mod_cast inner_re_symm (𝕜 := ℂ) p.1 p.2
  simp only [canonicalCompletedNativeProjectiveChiralForm,inner_smul_right,
    inner_sub_left,inner_add_right]
  norm_num [Complex.mul_re,Complex.sub_re,Complex.add_re,hc]

/-- The same response flux gives the WHOLE source, before the TFVD split.
It is a signed pairing, never an assertion of positivity. -/
theorem full_response_flux {N : ℕ} (k : ℕ) (c : ℕ →₀ ℂ)
    (hc : c.support ⊆ Finset.range N)
    (hF : ∀ j : Fin N, completedNativeOperatorCharacteristic
      (canonicalCompletedC3RadialTiltPoint k j) ≠ 0)
    (hd : ∀ j : ℕ, j < N → incidentWeight k j-returnedWeight k j=chiralDifference) :
    fullEnergy k c = 2*((k : ℝ)+1) *
      (inner ℂ (physicalCauchySynthesis c)
        (physicalCauchySynthesis (coefficientWeight (responseWeight k) c))).im := by
  unfold fullEnergy
  rw [signed_energy_mean,completed_source_contrast k c hc hd,
    source_mean_response k c hc hF hd,inner_smul_left,inner_smul_right,
    ← mul_assoc,source_scale_product]
  simp [Complex.mul_re,Complex.mul_im]

end
end CarryCriticalTfvd
