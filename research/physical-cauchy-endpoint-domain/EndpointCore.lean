import CarrySelfAdjointOperator.NativeCauchyLaguerreHeadTail
import CarrySelfAdjointOperator.NativePhysicalEndpointEncoder

/-! Algebraic material traces on the ORIGINAL half-density span. The
inverse below is justified by injectivity, not by a norm fit. No endpoint
evaluation of arbitrary Lp representatives is introduced. -/
namespace CarryPhysicalTrace
open CarrySelfAdjointOperator CarrySelfAdjointOperator.NativeLaguerre
open CPFormal.Analytic.Cp
open scoped BigOperators ComplexConjugate
noncomputable section
set_option autoImplicit false

theorem embedding_sum (c : ℕ →₀ ℂ) :
    physicalCauchyEmbedding c = c.sum (fun j a => a • physicalCauchyFeature j) := by
  apply Subtype.ext
  simp [physicalCauchySynthesis, Finsupp.linearCombination_apply,
    Finsupp.sum, physicalCauchyFeature_coe]

theorem embedding_eq_finite (c : ℕ →₀ ℂ) (N : ℕ)
    (hN : c.support ⊆ Finset.range N) :
    physicalCauchyEmbedding c = physicalFiniteSynthesis N (fun j => c j.val) := by
  rw [embedding_sum, Finsupp.sum_of_support_subset c hN _ (by simp)]
  exact (Fin.sum_univ_eq_sum_range (fun j => c j • physicalCauchyFeature j) N).symm

theorem physical_embedding_eq_zero (c : ℕ →₀ ℂ)
    (hc : physicalCauchyEmbedding c = 0) : c = 0 := by
  obtain ⟨N,hN⟩ := Finset.exists_nat_subset_range c.support
  have hz : physicalFiniteSynthesis N (fun j => c j.val) = physicalFiniteSynthesis N 0 := by
    rw [← embedding_eq_finite c N hN, hc, map_zero]
  have hv := physicalFiniteSynthesis_injective N hz
  ext j
  by_cases hj : j < N
  · exact congrFun hv ⟨j,hj⟩
  · have hnot : j ∉ c.support := by
      intro hm
      exact hj (Finset.mem_range.mp (hN hm))
    simpa only [Finsupp.mem_support_iff, ne_eq, not_not, Finsupp.zero_apply] using hnot

theorem physical_embedding_injective : Function.Injective physicalCauchyEmbedding := by
  intro c d h
  have hz : physicalCauchyEmbedding (c-d) = 0 := by rw [map_sub, h, sub_self]
  exact sub_eq_zero.mp (physical_embedding_eq_zero _ hz)

abbrev EndpointDomain := physicalCauchyEmbedding.range

def coefficientEquiv : (ℕ →₀ ℂ) ≃ₗ[ℂ] EndpointDomain :=
  LinearEquiv.ofInjective physicalCauchyEmbedding physical_embedding_injective

theorem coefficient_equiv_coe (c : ℕ →₀ ℂ) :
    (coefficientEquiv c : PhysicalCauchySpace) = physicalCauchyEmbedding c := rfl

theorem endpoint_domain_dense : DenseRange (fun x : EndpointDomain => (x : PhysicalCauchySpace)) := by
  apply physicalCauchyEmbedding_dense.mono
  rintro x ⟨c,rfl⟩
  exact ⟨coefficientEquiv c,rfl⟩

def coefficientEndpoint (a : ℕ) : (ℕ →₀ ℂ) →ₗ[ℂ] ℂ :=
  Finsupp.linearCombination ℂ (fun j => (j.descFactorial a : ℂ))

def endpointTrace (a : ℕ) : EndpointDomain →ₗ[ℂ] ℂ :=
  (coefficientEndpoint a).comp coefficientEquiv.symm.toLinearMap

/-- The separate material Dirichlet readout. It is not silently identified
with the endpoint value or with the completed characteristic readout. -/
def coefficientDirichlet (s : ℂ) : (ℕ →₀ ℂ) →ₗ[ℂ] ℂ :=
  Finsupp.linearCombination ℂ (positiveDirichletValue s)

def dirichletTrace (s : ℂ) : EndpointDomain →ₗ[ℂ] ℂ :=
  (coefficientDirichlet s).comp coefficientEquiv.symm.toLinearMap

def domainColumn (j : ℕ) : EndpointDomain := coefficientEquiv (Finsupp.single j 1)

theorem domain_column_coe (j : ℕ) : (domainColumn j : PhysicalCauchySpace) =
    physicalCauchyFeature j := rfl

theorem endpoint_trace_coefficients (a : ℕ) (c : ℕ →₀ ℂ) :
    endpointTrace a (coefficientEquiv c) = c.sum (fun j z => (j.descFactorial a : ℂ)*z) := by
  simp [endpointTrace, coefficientEndpoint, Finsupp.linearCombination_apply,
    smul_eq_mul, mul_comm]

theorem endpoint_trace_column (a j : ℕ) :
    endpointTrace a (domainColumn j) = (j.descFactorial a : ℂ) := by
  simp [endpointTrace, domainColumn, coefficientEndpoint]

theorem dirichlet_trace_column (s : ℂ) (j : ℕ) :
    dirichletTrace s (domainColumn j) = positiveDirichletValue s j := by
  simp [dirichletTrace, domainColumn, coefficientDirichlet]

theorem physical_column_inner (i j : ℕ) :
    inner ℂ (physicalCauchyFeature i) (physicalCauchyFeature j) =
      ((((i+j+2 : ℕ) : ℝ))⁻¹ : ℂ) := by
  change inner ℂ (physicalCauchyFeature i : CanonicalCompletedNativeChiralCauchyCarrier)
    (physicalCauchyFeature j : CanonicalCompletedNativeChiralCauchyCarrier) = _
  rw [physicalCauchyFeature_coe, physicalCauchyFeature_coe,
    inner_completedNativeChiralCauchyFeature]

theorem physical_column_norm_sq (j : ℕ) :
    ‖physicalCauchyFeature j‖^2 = (((j+j+2 : ℕ) : ℝ))⁻¹ := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), physical_column_inner]
  norm_cast

theorem physical_column_norm (j : ℕ) :
    ‖physicalCauchyFeature j‖ = Real.sqrt ((((j+j+2 : ℕ) : ℝ))⁻¹) := by
  rw [← physical_column_norm_sq]
  exact (Real.sqrt_sq (norm_nonneg _)).symm

end
end CarryPhysicalTrace
