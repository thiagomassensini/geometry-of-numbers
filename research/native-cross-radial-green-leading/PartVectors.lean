import PairExpansion
import CarrySelfAdjointOperator.CompletedNativeChiralJetEnergyControl

namespace CarryGreenLeading
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryCommutatorControl
open CarryEnergyCorrection NativeLaguerre NativeCauchyPorts
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000

/-- Literal single-leg fields from the EXISTING Green/boundary/commutator split.
This only names the three operators already inside completedSourceParts. -/
def partField (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) (w : ℕ → ℂ)
    (c : ℕ →₀ ℂ) : Fin 3 → CanonicalCompletedNativeChiralCauchyCarrier :=
  fun a => if a=0 then physicalGreenOperator eta h0.le h1
      (physicalCauchySynthesis (coefficientWeight w (finiteTfvdBulk eta c)))
  else if a=1 then ((physicalGreenResolvent eta h0.le h1)^2)
      ((w 0*c 0) • completedNativeChiralCauchyFeature 0+
        (w 1*c 1-2*(eta:ℂ)*(w 0*c 0)) • completedNativeChiralCauchyFeature 1)
  else physicalGreenOperator eta h0.le h1
      (physicalCauchySynthesis (completionCommutator eta w c))

theorem part_field_reconstruction (eta : ℝ) (h0 : 0<eta) (h1 : eta<1)
    (w : ℕ → ℂ) (c : ℕ →₀ ℂ) :
    ∑ a : Fin 3, partField eta h0 h1 w c a=
      physicalCauchySynthesis (coefficientWeight w c) := by
  simpa [Fin.sum_univ_three,partField] using
      (weighted_physical_reconstruction eta h0 h1 w c).symm

theorem part_field_add_weight (eta : ℝ) (h0 : 0<eta) (h1 : eta<1)
    (w v : ℕ → ℂ) (c : ℕ →₀ ℂ) (a : Fin 3) :
    partField eta h0 h1 (fun j => w j+v j) c a=
      partField eta h0 h1 w c a+partField eta h0 h1 v c a := by
  have hw := stencil_add_weight false eta w v (finiteTfvdBulk eta c)
  have hc := stencil_add_weight true eta w v c
  simp only [coefficientStencil,Bool.false_eq_true,ite_false,ite_true] at hw hc
  fin_cases a
  all_goals dsimp [partField]
  · rw [hw,map_add,map_add]
  · rw [← map_add]
    congr 1
    module
  · rw [hc,map_add,map_add]

theorem part_field_scale_weight (eta : ℝ) (h0 : 0<eta) (h1 : eta<1)
    (z : ℂ) (w : ℕ → ℂ) (c : ℕ →₀ ℂ) (a : Fin 3) :
    partField eta h0 h1 (fun j => z*w j) c a=z • partField eta h0 h1 w c a := by
  have hw := stencil_scale_weight false eta z w (finiteTfvdBulk eta c)
  have hc := commutator_weight_scale eta z w c
  simp only [coefficientStencil,Bool.false_eq_true,ite_false] at hw
  fin_cases a
  all_goals dsimp [partField]
  · rw [hw,map_smul,map_smul]
  · rw [← map_smul]
    congr 1
    module
  · rw [hc,map_smul,map_smul]

theorem part_field_scale_input (eta : ℝ) (h0 : 0<eta) (h1 : eta<1)
    (z : ℂ) (w : ℕ → ℂ) (c : ℕ →₀ ℂ) (a : Fin 3) :
    partField eta h0 h1 w (z • c) a=z • partField eta h0 h1 w c a := by
  have hb : finiteTfvdBulk eta (z • c)=z • finiteTfvdBulk eta c := by
    ext j
    cases j with
    | zero => simp [finiteTfvdBulk_zero]
    | succ j => simp only [finiteTfvdBulk_succ,Finsupp.smul_apply,smul_eq_mul]; ring
  have hw := stencil_scale_input false eta z w (finiteTfvdBulk eta c)
  have hc := stencil_scale_input true eta z w c
  simp only [coefficientStencil,Bool.false_eq_true,ite_false,ite_true] at hw hc
  fin_cases a
  all_goals dsimp [partField]
  · rw [hb,hw,map_smul,map_smul]
  · rw [← map_smul]
    congr 1
    module
  · rw [hc,map_smul,map_smul]

/-- Locality uses the ACTUAL support of both c and its TFVD bulk, plus the
TWO traces. No outgoing neighbor is silently removed. -/
theorem part_field_finite_locality (eta : ℝ) (h0 : 0<eta) (h1 : eta<1)
    (c : ℕ →₀ ℂ) : ∃ N : ℕ, ∀ w v : ℕ → ℂ,
      (∀ j : Fin N, w j=v j) → ∀ a : Fin 3,
        partField eta h0 h1 w c a=partField eta h0 h1 v c a := by
  classical
  obtain ⟨N,hN⟩ := Finset.exists_nat_subset_range
    (c.support ∪ (finiteTfvdBulk eta c).support ∪ {0,1})
  refine ⟨N,?_⟩
  intro w v hw
  have hz (d : ℕ →₀ ℂ) (hd : d.support ⊆ Finset.range N) :
      coefficientWeight w d=coefficientWeight v d := by
    ext j
    simp only [coefficient_weight_apply]
    by_cases hj : j∈d.support
    · rw [hw ⟨j,Finset.mem_range.mp (hd hj)⟩]
    · rw [Finsupp.notMem_support_iff.mp hj]
      ring
  have hc : c.support ⊆ Finset.range N := by
    intro j hj; exact hN (by simp only [Finset.mem_union]; exact Or.inl (Or.inl hj))
  have hb : (finiteTfvdBulk eta c).support ⊆ Finset.range N := by
    intro j hj; exact hN (by simp only [Finset.mem_union]; exact Or.inl (Or.inr hj))
  have h0N : 0<N := Finset.mem_range.mp (hN (by simp))
  have h1N : 1<N := Finset.mem_range.mp (hN (by simp))
  have ht0 := hw ⟨0,h0N⟩
  have ht1 := hw ⟨1,h1N⟩
  have hbulk : partField eta h0 h1 w c 0=partField eta h0 h1 v c 0 := by
    simp [partField,hz _ hb]
  have htrace : partField eta h0 h1 w c 1=partField eta h0 h1 v c 1 := by
    simp [partField,ht0,ht1]
  intro a
  fin_cases a
  · exact hbulk
  · exact htrace
  · have hew := part_field_reconstruction eta h0 h1 w c
    have hev := part_field_reconstruction eta h0 h1 v c
    simp only [Fin.sum_univ_three,hz _ hc,hbulk,htrace] at hew hev
    exact add_left_cancel (hew.trans hev.symm)

/-- Coordinates of the SAME original two-channel source part. -/
theorem completed_part_as_fields (eta : ℝ) (h0 : 0<eta) (h1 : eta<1)
    (k : ℕ) (c : ℕ →₀ ℂ) (a : Fin 3) :
    completedSourceParts eta h0 h1 k c a=
      ((Real.sqrt ((k:ℝ)+1):ℂ) • partField eta h0 h1 (incidentWeight k) c a,
       (Real.sqrt ((k:ℝ)+1):ℂ) • partField eta h0 h1 (returnedWeight k) c a) := by
  fin_cases a <;> rfl

theorem completed_part_scale_input (eta : ℝ) (h0 : 0<eta) (h1 : eta<1)
    (k : ℕ) (z : ℂ) (c : ℕ →₀ ℂ) (a : Fin 3) :
    completedSourceParts eta h0 h1 k (z • c) a=z • completedSourceParts eta h0 h1 k c a := by
  rw [completed_part_as_fields,completed_part_as_fields]
  simp only [part_field_scale_input,Prod.smul_mk,smul_smul]
  congr 1 <;> congr 1 <;> ring

/-- Exact vanishing of the CONSTANT response commutator; not deletion of its
variable response or its crossings. -/
theorem part_constant_residual_zero (eta : ℝ) (h0 : 0<eta) (h1 : eta<1)
    (c : ℕ →₀ ℂ) : partField eta h0 h1 (fun _ => 1) c 2=0 := by
  simp [partField,completion_commutator_constant]

end
end CarryGreenLeading
