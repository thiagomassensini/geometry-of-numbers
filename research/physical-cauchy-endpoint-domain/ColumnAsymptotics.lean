import EndpointCore
import Mathlib.Analysis.InnerProductSpace.Adjoint

namespace CarryPhysicalTrace
open CarrySelfAdjointOperator CarrySelfAdjointOperator.NativeLaguerre
open Filter Topology
open scoped BigOperators ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem physical_column_tendsto_zero :
    Tendsto physicalCauchyFeature atTop (𝓝 (0 : PhysicalCauchySpace)) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have ha : Tendsto (fun j : ℕ => (j+j+2 : ℕ)) atTop atTop :=
    tendsto_atTop_mono (fun j => by dsimp; omega) tendsto_id
  have hi : Tendsto (fun j : ℕ => (((j+j+2 : ℕ) : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp ha)
  simpa only [Function.comp_def, physical_column_norm, Real.sqrt_zero] using
    Real.continuous_sqrt.continuousAt.tendsto.comp hi

/-- The trace is a genuine algebraic trace but is not closable in the
ambient L2 norm: a zero-convergent physical sequence has trace identically one. -/
theorem endpoint_graph_witness :
    Tendsto (fun j => (domainColumn j : PhysicalCauchySpace)) atTop (𝓝 0) ∧
    (∀ j, endpointTrace 0 (domainColumn j) = 1) := by
  constructor
  · simpa only [domain_column_coe] using physical_column_tendsto_zero
  · intro j; simpa using endpoint_trace_column 0 j

theorem no_bounded_endpoint_extension :
    ¬∃ L : PhysicalCauchySpace →L[ℂ] ℂ,
      ∀ f : EndpointDomain, L (f : PhysicalCauchySpace) = endpointTrace 0 f := by
  rintro ⟨L,hL⟩
  have hl (j : ℕ) : L (physicalCauchyFeature j) = 1 := by
    simpa only [domain_column_coe,endpoint_trace_column,Nat.descFactorial_zero,Nat.cast_one] using hL (domainColumn j)
  have hc := L.continuous.continuousAt.tendsto.comp physical_column_tendsto_zero
  simp only [Function.comp_def,map_zero,hl] at hc
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hc)

/-- Unit columns use the unchanged ambient norm. This normalization is
only a sequence testing continuity, never a new source or new moment family. -/
def unitColumn (j : ℕ) : PhysicalCauchySpace :=
  (Real.sqrt ((j+j+2 : ℕ) : ℝ) : ℂ) • physicalCauchyFeature j

theorem unit_column_norm (j : ℕ) : ‖unitColumn j‖ = 1 := by
  have hp : 0 < ((j+j+2 : ℕ) : ℝ) := by positivity
  have hs : ‖unitColumn j‖^2 = 1 := by
    rw [unitColumn,norm_smul,mul_pow,physical_column_norm_sq,
      Complex.norm_real,Real.norm_eq_abs,sq_abs,Real.sq_sqrt hp.le,
      mul_inv_cancel₀ hp.ne']
  nlinarith [norm_nonneg (unitColumn j)]

theorem unit_column_inner_sq (i j : ℕ) :
    ‖inner ℂ (physicalCauchyFeature i) (unitColumn j)‖^2 =
      ((j+j+2 : ℕ) : ℝ) / ((i+j+2 : ℕ) : ℝ)^2 := by
  rw [unitColumn,inner_smul_right (𝕜 := ℂ) (E := PhysicalCauchySpace),physical_column_inner,norm_mul,mul_pow,
    Complex.norm_real,Real.norm_eq_abs,sq_abs,Real.sq_sqrt (by positivity)]
  simp only [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ ((i+j+2 : ℕ) : ℝ))]
  ring

theorem unit_column_inner_bound (i j : ℕ) :
    ‖inner ℂ (physicalCauchyFeature i) (unitColumn j)‖ ≤
      Real.sqrt (2 * (((j+1 : ℕ) : ℝ))⁻¹) := by
  have hp : 0 < ((j+1 : ℕ) : ℝ) := by positivity
  have hq : 0 < ((i+j+2 : ℕ) : ℝ) := by positivity
  have hle : ((j+1 : ℕ) : ℝ) ≤ ((i+j+2 : ℕ) : ℝ) := by exact_mod_cast (by omega : j+1 ≤ i+j+2)
  have hd : ((j+j+2 : ℕ) : ℝ) = 2*((j+1 : ℕ) : ℝ) := by push_cast; ring
  have hh : ((j+j+2 : ℕ) : ℝ)/((i+j+2 : ℕ) : ℝ)^2 ≤ 2*(((j+1 : ℕ) : ℝ))⁻¹ := by
    change ((j+j+2 : ℕ) : ℝ)/((i+j+2 : ℕ) : ℝ)^2 ≤ 2/((j+1 : ℕ) : ℝ)
    apply (div_le_div_iff₀ (sq_pos_of_pos hq) hp).mpr
    rw [hd]
    nlinarith
  rw [← unit_column_inner_sq] at hh
  have hs := Real.sq_sqrt (by positivity : 0 ≤ 2*(((j+1 : ℕ) : ℝ))⁻¹)
  nlinarith [norm_nonneg (inner ℂ (physicalCauchyFeature i) (unitColumn j)),
    Real.sqrt_nonneg (2*(((j+1 : ℕ) : ℝ))⁻¹)]

theorem column_inner_unit_tendsto (i : ℕ) :
    Tendsto (fun j => inner ℂ (physicalCauchyFeature i) (unitColumn j)) atTop (𝓝 0) := by
  apply squeeze_zero_norm (unit_column_inner_bound i)
  have ha : Tendsto (fun j : ℕ => (j+1 : ℕ)) atTop atTop :=
    tendsto_atTop_mono (fun j => by dsimp; omega) tendsto_id
  have hi : Tendsto (fun j : ℕ => (((j+1 : ℕ) : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp ha)
  simpa only [Function.comp_def,mul_zero,Real.sqrt_zero] using
    Real.continuous_sqrt.continuousAt.tendsto.comp (tendsto_const_nhds.mul hi)

theorem finite_inner_unit_tendsto (c : ℕ →₀ ℂ) :
    Tendsto (fun j => inner ℂ (physicalCauchyEmbedding c) (unitColumn j)) atTop (𝓝 0) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simpa only [map_add,inner_add_left,add_zero] using hc.add hd
  | single i a =>
      have he : physicalCauchyEmbedding (Finsupp.single i a) = a • physicalCauchyFeature i := by
        rw [embedding_sum]
        simp
      simp only [he,inner_smul_left (𝕜 := ℂ) (E := PhysicalCauchySpace)]
      simpa using tendsto_const_nhds.mul (column_inner_unit_tendsto i)

/-- Weak convergence tested on every vector of the ORIGINAL physical closure. -/
theorem unit_column_weak_zero (v : PhysicalCauchySpace) :
    Tendsto (fun j => inner ℂ v (unitColumn j)) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨c,hc⟩ := physicalCauchyEmbedding_dense.exists_dist_lt v (half_pos hε)
  have he := Metric.tendsto_nhds.mp (finite_inner_unit_tendsto c) (ε/2) (half_pos hε)
  filter_upwards [he] with j hj
  rw [dist_zero_right] at hj ⊢
  have hi := norm_inner_le_norm (𝕜 := ℂ) (v-physicalCauchyEmbedding c) (unitColumn j)
  rw [unit_column_norm,mul_one] at hi
  rw [dist_eq_norm] at hc
  have hs : inner ℂ v (unitColumn j) =
      inner ℂ (v-physicalCauchyEmbedding c) (unitColumn j) +
        inner ℂ (physicalCauchyEmbedding c) (unitColumn j) := by rw [inner_sub_left]; abel
  rw [hs]
  exact lt_of_le_of_lt (norm_add_le _ _) (by linarith)

theorem bounded_readout_unit_tendsto_zero (L : PhysicalCauchySpace →L[ℂ] ℂ) :
    Tendsto (fun j => L (unitColumn j)) atTop (𝓝 0) := by
  have h := unit_column_weak_zero ((ContinuousLinearMap.adjoint L) 1)
  simpa only [ContinuousLinearMap.adjoint_inner_left,RCLike.inner_apply,
    map_one,mul_one] using h

end
end CarryPhysicalTrace
