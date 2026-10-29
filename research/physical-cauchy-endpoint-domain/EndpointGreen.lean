import EndpointCore

/-! This is the Euler action of the material POLYNOMIAL p + X p'.
It is not the material logarithmic clock, the carry depth, or an
identified generator of canonical moments. The ambient metric is unchanged. -/
namespace CarryPhysicalTrace
open CarrySelfAdjointOperator CarrySelfAdjointOperator.NativeLaguerre
open scoped BigOperators ComplexConjugate
noncomputable section
set_option autoImplicit false

def coefficientEuler : (ℕ →₀ ℂ) →ₗ[ℂ] (ℕ →₀ ℂ) :=
  Finsupp.linearCombination ℂ (fun j => ((j+1 : ℕ) : ℂ) • Finsupp.single j 1)

theorem coefficient_euler_single (j : ℕ) (a : ℂ) :
    coefficientEuler (Finsupp.single j a) = Finsupp.single j (((j+1 : ℕ) : ℂ)*a) := by
  simp only [coefficientEuler, Finsupp.linearCombination_single,
    Finsupp.smul_single, smul_eq_mul, mul_one]
  congr 1
  ring

theorem coefficient_euler_apply (c : ℕ →₀ ℂ) (j : ℕ) :
    coefficientEuler c j = ((j+1 : ℕ) : ℂ)*c j := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp [hc,hd,mul_add]
  | single i a =>
      rw [coefficient_euler_single]
      by_cases h : i=j
      · subst j; simp
      · simp [h]

def eulerAction : EndpointDomain →ₗ[ℂ] EndpointDomain :=
  coefficientEquiv.toLinearMap.comp (coefficientEuler.comp coefficientEquiv.symm.toLinearMap)

theorem euler_action_coefficients (c : ℕ →₀ ℂ) :
    (eulerAction (coefficientEquiv c) : PhysicalCauchySpace) =
      physicalCauchyEmbedding (coefficientEuler c) := by
  simp [eulerAction,coefficient_equiv_coe]

theorem physical_embedding_single (j : ℕ) (a : ℂ) :
    physicalCauchyEmbedding (Finsupp.single j a) = a • physicalCauchyFeature j := by
  have h : Finsupp.single j a = a • Finsupp.single j 1 := by simp
  rw [h,map_smul]
  rfl

/-- Two independent coefficient arguments, with the original Cauchy crosses. -/
theorem physical_euler_green (c d : ℕ →₀ ℂ) :
    conj (coefficientEndpoint 0 c) * coefficientEndpoint 0 d =
      inner ℂ (physicalCauchyEmbedding (coefficientEuler c)) (physicalCauchyEmbedding d) +
      inner ℂ (physicalCauchyEmbedding c) (physicalCauchyEmbedding (coefficientEuler d)) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c e hc he =>
      simp only [map_add, inner_add_left, hc, he, add_mul]
      ring
  | single i a =>
      induction d using Finsupp.induction_linear with
      | zero => simp
      | add d e hd he =>
          simp only [map_add, inner_add_right, mul_add, hd, he]
          ring
      | single j b =>
          rw [coefficient_euler_single,coefficient_euler_single]
          have hi : coefficientEndpoint 0 (Finsupp.single i a) = a := by simp [coefficientEndpoint]
          have hj : coefficientEndpoint 0 (Finsupp.single j b) = b := by simp [coefficientEndpoint]
          rw [hi,hj]
          simp only [physical_embedding_single]
          rw [_root_.inner_smul_left (𝕜 := ℂ) (E := PhysicalCauchySpace),
            _root_.inner_smul_left (𝕜 := ℂ) (E := PhysicalCauchySpace),
            _root_.inner_smul_right (𝕜 := ℂ) (E := PhysicalCauchySpace),
            _root_.inner_smul_right (𝕜 := ℂ) (E := PhysicalCauchySpace),physical_column_inner]
          simp only [map_mul, map_natCast]
          have hn : ((i+j+2 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : i+j+2 ≠ 0)
          push_cast at hn ⊢
          field_simp [hn]
          ring

theorem endpoint_green (f g : EndpointDomain) :
    conj (endpointTrace 0 f) * endpointTrace 0 g =
      inner ℂ (eulerAction f : PhysicalCauchySpace) (g : PhysicalCauchySpace) +
      inner ℂ (f : PhysicalCauchySpace) (eulerAction g : PhysicalCauchySpace) := by
  obtain ⟨c,rfl⟩ := coefficientEquiv.surjective f
  obtain ⟨d,rfl⟩ := coefficientEquiv.surjective g
  simpa [endpointTrace,euler_action_coefficients,coefficient_equiv_coe] using physical_euler_green c d

theorem endpoint_green_energy (f : EndpointDomain) :
    ‖endpointTrace 0 f‖^2 =
      2 * (inner ℂ (f : PhysicalCauchySpace) (eulerAction f : PhysicalCauchySpace)).re := by
  have h := congrArg Complex.re (endpoint_green f f)
  have hr : (inner ℂ (eulerAction f : PhysicalCauchySpace) (f : PhysicalCauchySpace)).re =
      (inner ℂ (f : PhysicalCauchySpace) (eulerAction f : PhysicalCauchySpace)).re :=
    _root_.inner_re_symm (𝕜 := ℂ) (E := PhysicalCauchySpace) _ _
  simp only [Complex.add_re] at h
  rw [hr] at h
  rw [← two_mul] at h
  rw [← h]
  rw [Complex.sq_norm]
  simp [Complex.normSq_apply,Complex.mul_re]

theorem endpoint_graph_bound (f : EndpointDomain) :
    ‖endpointTrace 0 f‖^2 ≤
      ‖(f : PhysicalCauchySpace)‖^2 + ‖(eulerAction f : PhysicalCauchySpace)‖^2 := by
  rw [endpoint_green_energy]
  have h := Complex.re_le_norm (inner ℂ (f : PhysicalCauchySpace) (eulerAction f : PhysicalCauchySpace))
  have h' := norm_inner_le_norm (𝕜 := ℂ) (f : PhysicalCauchySpace) (eulerAction f : PhysicalCauchySpace)
  nlinarith [sq_nonneg (‖(f : PhysicalCauchySpace)‖ - ‖(eulerAction f : PhysicalCauchySpace)‖)]

end
end CarryPhysicalTrace
