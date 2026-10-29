import ResponseTaylor

namespace CarryCriticalTfvd
open CarrySelfAdjointOperator CarryNativeTfvd CarryCommutatorControl NativeLaguerre
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000

/-- Two diagnostics of the SAME source: false is its whole response flux;
true is its PR93 Green-commutator flux. No new source or metric is supplied. -/
def coefficientStencil (mixed : Bool) (eta : ℝ) (w : ℕ → ℂ) (c : ℕ →₀ ℂ) : ℕ →₀ ℂ :=
  if mixed then completionCommutator eta w c else coefficientWeight w c

def sectorField (mixed : Bool) (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (w : ℕ → ℂ) (c : ℕ →₀ ℂ) : CanonicalCompletedNativeChiralCauchyCarrier :=
  if mixed then physicalGreenOperator eta h0.le h1 (physicalCauchySynthesis (coefficientStencil mixed eta w c))
  else physicalCauchySynthesis (coefficientStencil mixed eta w c)

def sectorKernel (mixed : Bool) (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (w : ℕ → ℂ) (c d : ℕ →₀ ℂ) : ℂ := inner ℂ (physicalCauchySynthesis c)
      (sectorField mixed eta h0 h1 w d)

theorem stencil_add_weight (mixed : Bool) (eta : ℝ) (w z : ℕ → ℂ) (c : ℕ →₀ ℂ) :
    coefficientStencil mixed eta (fun j => w j+z j) c =
      coefficientStencil mixed eta w c + coefficientStencil mixed eta z c := by
  cases mixed
  · ext j; simp [coefficientStencil,coefficient_weight_apply]; ring
  · ext j; cases j with
    | zero => simp [coefficientStencil,completion_commutator_zero]
    | succ j => simp only [coefficientStencil,ite_true,completion_commutator_succ,Finsupp.add_apply]; ring

theorem stencil_scale_weight (mixed : Bool) (eta : ℝ) (a : ℂ) (w : ℕ → ℂ) (c : ℕ →₀ ℂ) :
    coefficientStencil mixed eta (fun j => a*w j) c = a • coefficientStencil mixed eta w c := by
  cases mixed
  · ext j; simp [coefficientStencil,coefficient_weight_apply]; ring
  · exact commutator_weight_scale eta a w c

theorem stencil_add_input (mixed : Bool) (eta : ℝ) (w : ℕ → ℂ) (c d : ℕ →₀ ℂ) :
    coefficientStencil mixed eta w (c+d) =
      coefficientStencil mixed eta w c + coefficientStencil mixed eta w d := by
  cases mixed
  · ext j; simp [coefficientStencil,coefficient_weight_apply]; ring
  · ext j; cases j with
    | zero => simp [coefficientStencil,completion_commutator_zero]
    | succ j => simp only [coefficientStencil,ite_true,completion_commutator_succ,Finsupp.add_apply]; ring

theorem stencil_scale_input (mixed : Bool) (eta : ℝ) (a : ℂ) (w : ℕ → ℂ) (c : ℕ →₀ ℂ) :
    coefficientStencil mixed eta w (a • c) = a • coefficientStencil mixed eta w c := by
  cases mixed
  · ext j; simp [coefficientStencil,coefficient_weight_apply]; ring
  · ext j; cases j with
    | zero => simp [coefficientStencil,completion_commutator_zero]
    | succ j => simp only [coefficientStencil,ite_true,completion_commutator_succ,Finsupp.smul_apply,smul_eq_mul]; ring

theorem stencil_congr {N : ℕ} (mixed : Bool) (eta : ℝ) (w z : ℕ → ℂ) (c : ℕ →₀ ℂ)
    (hc : c.support ⊆ Finset.range N) (he : ∀ j : Fin (N+1), w j=z j) :
    coefficientStencil mixed eta w c=coefficientStencil mixed eta z c := by
  cases mixed
  · ext j
    change w j*c j=z j*c j
    by_cases hj : j<N
    · rw [he ⟨j,by omega⟩]
    · rw [coefficient_outside_prefix c hc j (by omega)]
      simp
  · apply commutator_equal_of_constant_difference eta w z 0 c hc
    intro j hj; rw [he ⟨j,hj⟩]; ring

theorem field_add_weight (mixed : Bool) (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (w z : ℕ → ℂ) (c : ℕ →₀ ℂ) :
    sectorField mixed eta h0 h1 (fun j => w j+z j) c =
      sectorField mixed eta h0 h1 w c + sectorField mixed eta h0 h1 z c := by
  cases mixed <;> simp [sectorField,stencil_add_weight,map_add]

theorem field_scale_weight (mixed : Bool) (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (a : ℂ) (w : ℕ → ℂ) (c : ℕ →₀ ℂ) :
    sectorField mixed eta h0 h1 (fun j => a*w j) c = a • sectorField mixed eta h0 h1 w c := by
  cases mixed <;> simp [sectorField,stencil_scale_weight,map_smul]

theorem field_add_input (mixed : Bool) (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (w : ℕ → ℂ) (c d : ℕ →₀ ℂ) :
    sectorField mixed eta h0 h1 w (c+d) =
      sectorField mixed eta h0 h1 w c + sectorField mixed eta h0 h1 w d := by
  cases mixed <;> simp [sectorField,stencil_add_input,map_add]

theorem field_scale_input (mixed : Bool) (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (a : ℂ) (w : ℕ → ℂ) (c : ℕ →₀ ℂ) :
    sectorField mixed eta h0 h1 w (a • c) = a • sectorField mixed eta h0 h1 w c := by
  cases mixed <;> simp [sectorField,stencil_scale_input,map_smul]

theorem kernel_add_weight (mixed : Bool) (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (w z : ℕ → ℂ) (c d : ℕ →₀ ℂ) :
    sectorKernel mixed eta h0 h1 (fun j => w j+z j) c d =
      sectorKernel mixed eta h0 h1 w c d + sectorKernel mixed eta h0 h1 z c d := by
  simp only [sectorKernel,field_add_weight,inner_add_right]

theorem kernel_scale_weight (mixed : Bool) (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (a : ℂ) (w : ℕ → ℂ) (c d : ℕ →₀ ℂ) :
    sectorKernel mixed eta h0 h1 (fun j => a*w j) c d = a*sectorKernel mixed eta h0 h1 w c d := by
  simp only [sectorKernel,field_scale_weight,inner_smul_right]

theorem kernel_four_weights (mixed : Bool) (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (a b c d : ℂ) (w x y z : ℕ → ℂ) (u v : ℕ →₀ ℂ) :
    sectorKernel mixed eta h0 h1 (fun j => a*w j+b*x j+c*y j+d*z j) u v =
      a*sectorKernel mixed eta h0 h1 w u v+b*sectorKernel mixed eta h0 h1 x u v+
      c*sectorKernel mixed eta h0 h1 y u v+d*sectorKernel mixed eta h0 h1 z u v := by
  simp only [kernel_add_weight,kernel_scale_weight]

def spatialU (mixed : Bool) (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (w : ℕ → ℂ) : ℝ :=
  (sectorKernel mixed eta h0 h1 w curvatureInput curvatureInput).re
def spatialV (mixed : Bool) (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (w : ℕ → ℂ) : ℝ :=
  (sectorKernel mixed eta h0 h1 w curvatureInput seedInput +
   sectorKernel mixed eta h0 h1 w seedInput curvatureInput).re
def spatialW (mixed : Bool) (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (w : ℕ → ℂ) : ℝ :=
  (sectorKernel mixed eta h0 h1 w seedInput seedInput).re

theorem kernel_critical_real (mixed : Bool) (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (w : ℕ → ℂ) (k : ℕ) (a : ℝ) :
    (sectorKernel mixed eta h0 h1 w (criticalInput k a) (criticalInput k a)).re =
      ((k : ℝ)+1)^4*spatialU mixed eta h0 h1 w +
      a*((k : ℝ)+1)^2*spatialV mixed eta h0 h1 w+a^2*spatialW mixed eta h0 h1 w := by
  have hs : (((k : ℝ)+1)^2 : ℂ) = ((((k : ℝ)+1)^2 : ℝ) : ℂ) := by push_cast; rfl
  simp only [criticalInput,hs,sectorKernel,map_add,map_smul,field_add_input,field_scale_input,
    inner_add_left,inner_add_right,inner_smul_left,inner_smul_right,Complex.conj_ofReal]
  simp only [spatialU,spatialV,spatialW,sectorKernel,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero,Complex.add_re]
  ring

theorem weight_triple (w : ℕ → ℂ) (a b c : ℂ) :
    coefficientWeight w (triple a b c)=triple (w 0*a) (w 1*b) (w 2*c) := by
  ext j
  rcases j with _ | _ | _ | j <;> simp [triple,coefficient_weight_apply]

/-- Only the four retained addresses occur. This supplies a genuine analytic
remainder bound on the original physical kernel, including its Green factor. -/
theorem remainder_field_continuous (mixed : Bool) (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (R : ℂ → ℂ) (hR : AnalyticAt ℂ R 0) (a b c : ℂ) :
    ContinuousAt (fun t : ℝ => sectorField mixed eta h0 h1 (remainderWeight R t) (triple a b c)) 0 := by
  have hr (j : ℕ) : ContinuousAt (fun t : ℝ => remainderWeight R t j) 0 := by
    have ht : Tendsto (fun t : ℝ => ((j+1 : ℕ) : ℂ)*(t : ℂ)) (nhds 0) (nhds 0) := by
      have hh : ContinuousAt (fun t : ℝ => ((j+1 : ℕ) : ℂ)*(t : ℂ)) 0 := by fun_prop
      simpa using hh.tendsto
    have hh : ContinuousAt (fun t : ℝ => R (((j+1 : ℕ) : ℂ)*(t : ℂ))) 0 := by
      simpa only [ContinuousAt,mul_zero,Complex.ofReal_zero,Function.comp_def] using
        hR.continuousAt.tendsto.comp ht
    unfold remainderWeight
    exact continuousAt_const.mul hh
  have hr0 := hr 0; have hr1 := hr 1; have hr2 := hr 2; have hr3 := hr 3
  cases mixed
  · simp only [sectorField,coefficientStencil,Bool.false_eq_true,ite_false,weight_triple,synthesis_triple]
    fun_prop
  · simp only [sectorField,coefficientStencil,ite_true,commutator_triple,
      physicalCauchySynthesis,map_add,Finsupp.linearCombination_single,map_smul]
    fun_prop

theorem remainder_kernel_continuous (mixed : Bool) (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (R : ℂ → ℂ) (hR : AnalyticAt ℂ R 0) (u : ℕ →₀ ℂ) (a b c : ℂ) :
    ContinuousAt (fun t : ℝ =>
      (sectorKernel mixed eta h0 h1 (remainderWeight R t) u (triple a b c)).re) 0 := by
  have hr := remainder_field_continuous mixed eta h0 h1 R hR a b c
  unfold sectorKernel
  fun_prop

end
end CarryCriticalTfvd
