import CompletedTfvdTransport
import DomainCompatibility

/-! A readout is applied only after the WHOLE corrected Green synthesis has
returned to the physical algebraic domain. No functional on arbitrary Lp is invented. -/
namespace CarryRadialGreen
open CarryPhysicalTrace CarryRadialRefinement CarrySelfAdjointOperator
open CarrySelfAdjointOperator.NativeLaguerre CPFormal.Analytic.Cp
open scoped BigOperators ComplexConjugate InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

abbrev CorePair := EndpointDomain × EndpointDomain

def corePairEmbedding : CorePair →ₗ[ℂ] PhysicalPair where
  toFun u := (u.1.val,u.2.val)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def projectiveCore (k j : ℕ) : CorePair :=
  ((completedNativeNormalizedPositiveChiralAmplitude (canonicalCompletedC3RadialTiltPoint k j)*
      (Real.sqrt ((k : ℝ)+1) : ℂ)) • domainColumn j,
   (completedNativeNormalizedPositiveChiralAmplitude (canonicalCompletedC3RadialTiltPoint k j)*
      completedNativeHermiteBiehlerChiralQuotient (canonicalCompletedC3RadialTiltPoint k j)*
      (Real.sqrt ((k : ℝ)+1) : ℂ)) • domainColumn j)

theorem projective_core_coe (k j : ℕ) :
    corePairEmbedding (projectiveCore k j) = projectiveLegs k j := by
  apply Prod.ext <;>
    simp only [corePairEmbedding,LinearMap.coe_mk,AddHom.coe_mk,projectiveCore,
      Submodule.coe_smul,domain_column_coe,projectiveLegs,radial_vector_feature,smul_smul]

def completedCoreSource (k : ℕ) : (ℕ →₀ ℂ) →ₗ[ℂ] CorePair :=
  Finsupp.linearCombination ℂ (projectiveCore k)

theorem completed_core_source_coe (k : ℕ) (x : ℕ →₀ ℂ) :
    corePairEmbedding (completedCoreSource k x) = completedSource k x := by
  simp only [completedCoreSource,completedSource,Finsupp.linearCombination_apply,Finsupp.sum,
    map_sum,map_smul,projective_core_coe]

def pairCorePower (m : ℕ) : CorePair →ₗ[ℂ] CorePair where
  toFun u := (powerCore m u.1,powerCore m u.2)
  map_add' _ _ := by apply Prod.ext <;> simp
  map_smul' _ _ := by apply Prod.ext <;> simp

theorem pair_core_power_coe (m : ℕ) (u : CorePair) :
    corePairEmbedding (pairCorePower m u) = pairPower m (corePairEmbedding u) := by
  apply Prod.ext <;> exact power_core_coe m _

def materialPairReadout (s : ℂ) (u : CorePair) : ℂ × ℂ :=
  (dirichletTrace s u.1,dirichletTrace s u.2)

theorem material_readout_power (s : ℂ) (m : ℕ) (x : EndpointDomain) :
    dirichletTrace s (powerCore m x) =
      ((Real.sqrt ((m : ℝ)+1) : ℂ)*positiveDirichletValue s m)*dirichletTrace s x := by
  obtain ⟨c,rfl⟩ := coefficientEquiv.surjective x
  simp only [powerCore,dirichletTrace,LinearMap.comp_apply,LinearEquiv.coe_toLinearMap,
    LinearEquiv.symm_apply_apply]
  exact dirichlet_power_coefficient s m c

/-- This witness is the original finite source, transported by the already
proved core isometry. Its existence follows from complete Green reconstruction. -/
theorem whole_green_material_readout (s : ℂ) (m : ℕ) (η : ℝ)
    (hη0 : 0 < η) (hη1 : η < 1) (k : ℕ) (x : ℕ →₀ ℂ) :
    ∃ u : CorePair,
      corePairEmbedding u = (η : ℂ) • ((pairResolvent (m+1) η)^2)
        (pairPower m (bulkBoundary η k x)+pairPower m (residualNumerator η k x)) ∧
      materialPairReadout s u =
        ((Real.sqrt ((m : ℝ)+1) : ℂ)*positiveDirichletValue s m) •
          materialPairReadout s (completedCoreSource k x) := by
  refine ⟨pairCorePower m (completedCoreSource k x),?_,?_⟩
  · rw [pair_core_power_coe,completed_core_source_coe,refined_completed_reconstruct m η hη0 hη1 k x]
  · apply Prod.ext <;>
      simp only [materialPairReadout,pairCorePower,LinearMap.coe_mk,AddHom.coe_mk,
        material_readout_power,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]

theorem core_pair_embedding_injective : Function.Injective corePairEmbedding := by
  intro x y h
  apply Prod.ext
  · apply Subtype.ext; exact congrArg Prod.fst h
  · apply Subtype.ext; exact congrArg Prod.snd h

/-- No arbitrary choice of a scalar readout extension is hidden in the witness. -/
theorem whole_green_core_witness_unique (m : ℕ) (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1)
    (k : ℕ) (x : ℕ →₀ ℂ) (u : CorePair)
    (hu : corePairEmbedding u = (η : ℂ) • ((pairResolvent (m+1) η)^2)
      (pairPower m (bulkBoundary η k x)+pairPower m (residualNumerator η k x))) :
    u = pairCorePower m (completedCoreSource k x) := by
  apply core_pair_embedding_injective
  rw [hu,pair_core_power_coe,completed_core_source_coe,
    refined_completed_reconstruct m η hη0 hη1 k x]

end
end CarryRadialGreen
