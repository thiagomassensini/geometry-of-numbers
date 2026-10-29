import RadialRefinement
import EndpointGreen

namespace CarryRadialRefinement
open CarryPhysicalTrace CarrySelfAdjointOperator CarrySelfAdjointOperator.NativeLaguerre
open CPFormal.Analytic.Cp
open scoped BigOperators ComplexConjugate InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

def powerCoefficient (m : ℕ) : (ℕ →₀ ℂ) →ₗ[ℂ] (ℕ →₀ ℂ) :=
  Finsupp.linearCombination ℂ (fun j =>
    (Real.sqrt ((m : ℝ)+1) : ℂ) • Finsupp.single (refinedAddress m j) 1)

theorem power_coefficient_single (m j : ℕ) (a : ℂ) :
    powerCoefficient m (Finsupp.single j a) =
      Finsupp.single (refinedAddress m j) ((Real.sqrt ((m : ℝ)+1) : ℂ)*a) := by
  simp [powerCoefficient,mul_comm]

theorem embedding_power_coefficient (m : ℕ) (c : ℕ →₀ ℂ) :
    physicalCauchyEmbedding (powerCoefficient m c) = powerSynthesis m c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add,hc,hd]
  | single j a =>
    rw [power_coefficient_single,physical_embedding_single]
    simp only [powerSynthesis,Finsupp.linearCombination_single,powerColumn,smul_smul]
    rw [mul_comm]

def powerCore (m : ℕ) : EndpointDomain →ₗ[ℂ] EndpointDomain :=
  coefficientEquiv.toLinearMap.comp ((powerCoefficient m).comp coefficientEquiv.symm.toLinearMap)

theorem power_core_coe (m : ℕ) (x : EndpointDomain) :
    (powerCore m x : PhysicalCauchySpace) = powerIsometry m (x : PhysicalCauchySpace) := by
  obtain ⟨c,rfl⟩ := coefficientEquiv.surjective x
  simp only [powerCore,LinearMap.comp_apply,LinearEquiv.coe_toLinearMap,
    LinearEquiv.symm_apply_apply,coefficient_equiv_coe]
  change physicalCauchyEmbedding (powerCoefficient m c) =
    powerExtension m (physicalCauchyEmbedding c)
  rw [embedding_power_coefficient,power_extension_synthesis]

/-- Domain preservation and the correct Euler scaling are proved explicitly.
This Euler action is NOT silently identified with the material log clock. -/
theorem coefficient_euler_power (m : ℕ) (c : ℕ →₀ ℂ) :
    coefficientEuler (powerCoefficient m c) =
      ((m+1 : ℕ) : ℂ) • powerCoefficient m (coefficientEuler c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add,hc,hd,smul_add]
  | single j a =>
    rw [power_coefficient_single,coefficient_euler_single,coefficient_euler_single,
      power_coefficient_single,refined_address_succ]
    simp only [Finsupp.smul_single,smul_eq_mul,Nat.cast_mul]
    congr 1
    ring

theorem euler_power_core (m : ℕ) (x : EndpointDomain) :
    eulerAction (powerCore m x) = ((m+1 : ℕ) : ℂ) • powerCore m (eulerAction x) := by
  obtain ⟨c,rfl⟩ := coefficientEquiv.surjective x
  simp only [eulerAction,powerCore,LinearMap.comp_apply,LinearEquiv.coe_toLinearMap,
    LinearEquiv.symm_apply_apply,coefficient_euler_power,map_smul]

theorem endpoint_power_coefficient (m : ℕ) (c : ℕ →₀ ℂ) :
    coefficientEndpoint 0 (powerCoefficient m c) =
      (Real.sqrt ((m : ℝ)+1) : ℂ)*coefficientEndpoint 0 c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add,hc,hd,mul_add]
  | single j a =>
    have he (i : ℕ) (z : ℂ) : coefficientEndpoint 0 (Finsupp.single i z) = z := by
      simp [coefficientEndpoint]
    rw [power_coefficient_single,he,he]

theorem positive_value_refined (s : ℂ) (m j : ℕ) :
    positiveDirichletValue s (refinedAddress m j) =
      positiveDirichletValue s m*positiveDirichletValue s j := by
  unfold positiveDirichletValue
  rw [refined_address_succ]
  simp only [Nat.cast_mul]
  simpa only [Complex.ofReal_natCast] using
    Complex.mul_cpow_ofReal_nonneg (by positivity : (0 : ℝ) ≤ ((m+1 : ℕ) : ℝ))
      (by positivity : (0 : ℝ) ≤ ((j+1 : ℕ) : ℝ)) (-s)

/-- The independent material readout is COVARIANT, not unchanged. Its complex
factor is retained. This prevents a false full-material invariance claim. -/
theorem dirichlet_power_coefficient (s : ℂ) (m : ℕ) (c : ℕ →₀ ℂ) :
    coefficientDirichlet s (powerCoefficient m c) =
      ((Real.sqrt ((m : ℝ)+1) : ℂ)*positiveDirichletValue s m)*coefficientDirichlet s c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add,hc,hd,mul_add]
  | single j a =>
    simp only [power_coefficient_single,coefficientDirichlet,Finsupp.linearCombination_single,
      smul_eq_mul,positive_value_refined]
    ring

/-- Critical compatibility preserves the modulus of the material readout's
factor, while the full complex factor above still preserves its phase. -/
theorem critical_dirichlet_factor_norm_sq (s : ℂ) (hs : s.re = 1/2) (m : ℕ) :
    ‖(Real.sqrt ((m : ℝ)+1) : ℂ)*positiveDirichletValue s m‖^2 = 1 := by
  have hp : 0 < ((m+1 : ℕ) : ℝ) := by positivity
  have hr : ((((m+1 : ℕ) : ℝ)^(-(1/2 : ℝ)))^2) = (((m+1 : ℕ) : ℝ))⁻¹ := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hp.le]
    norm_num [Real.rpow_neg_one]
  rw [norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,
    Real.sq_sqrt (by positivity),norm_positiveDirichletValue,hs,hr]
  norm_num only [Nat.cast_add,Nat.cast_one]
  field_simp

end
end CarryRadialRefinement
