import PhysicalAllOrder
import NativeRemainder

/-! Coefficients of the SAME completed native response on the SAME radial
nodes. Full source synthesis is established in PhysicalAllOrder first. -/
namespace CarryBinomialGreen
open CarryGreenFinitePart CarrySelfAdjointOperator Filter Topology
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192

def nodeRay (r s : ℕ) (z : ℂ) : ℂ :=
  ((r:ℂ)+(s:ℂ)+2)⁻¹ *
    (imaginaryReadout (((r:ℂ)+1)*z)+imaginaryReadout (((s:ℂ)+1)*z))

def rawRay (p q : ℕ) (z : ℂ) : ℂ :=
  ∑ r ∈ Finset.range (p+1), ∑ s ∈ Finset.range (q+1),
    ((realWeight p r*realWeight q s:ℝ):ℂ)*nodeRay r s z

theorem readout_dilation_analytic (a : ℂ) :
    AnalyticAt ℂ (fun z => imaginaryReadout (a*z)) 0 :=
  readout_analytic.fun_comp_of_eq (by fun_prop) (by simp)

theorem node_ray_analytic (r s : ℕ) : AnalyticAt ℂ (nodeRay r s) 0 :=
  analyticAt_const.mul ((readout_dilation_analytic _).add (readout_dilation_analytic _))

theorem raw_ray_analytic (p q : ℕ) : AnalyticAt ℂ (rawRay p q) 0 := by
  apply Finset.analyticAt_fun_sum
  intro r _
  apply Finset.analyticAt_fun_sum
  intro s _
  exact analyticAt_const.mul (node_ray_analytic r s)

theorem node_ray_coefficient (r s d : ℕ) :
    iteratedDeriv d (nodeRay r s) 0/(d.factorial:ℂ)=
      readoutCoefficient d*(((r:ℂ)+1)^d+((s:ℂ)+1)^d)/((r:ℂ)+(s:ℂ)+2) := by
  unfold nodeRay
  rw [iteratedDeriv_const_mul_field,
    iteratedDeriv_fun_add (readout_dilation_analytic _).contDiffAt (readout_dilation_analytic _).contDiffAt,
    iteratedDeriv_comp_mul_zero, iteratedDeriv_comp_mul_zero,
    ← readout_coefficient_derivative]
  ring

theorem raw_ray_derivative (p q d : ℕ) :
    iteratedDeriv d (rawRay p q) 0=
      ∑ r ∈ Finset.range (p+1), ∑ s ∈ Finset.range (q+1),
        ((realWeight p r*realWeight q s:ℝ):ℂ)*iteratedDeriv d (nodeRay r s) 0 := by
  unfold rawRay
  rw [iteratedDeriv_fun_sum]
  · apply Finset.sum_congr rfl
    intro r _
    rw [iteratedDeriv_fun_sum]
    · apply Finset.sum_congr rfl
      intro s _
      exact iteratedDeriv_const_mul_field _ _
    · intro s _
      exact (analyticAt_const.mul (node_ray_analytic r s)).contDiffAt
  · intro r _
    apply (Finset.analyticAt_fun_sum _ fun s _ => ?_).contDiffAt
    exact analyticAt_const.mul (node_ray_analytic r s)

/-- Coefficient extraction retains two independent stencils and every cross. -/
theorem raw_ray_coefficient (p q d : ℕ) :
    iteratedDeriv d (rawRay p q) 0/(d.factorial:ℂ)=
      readoutCoefficient d * (mixedStencil p q (fun x y => (x^d+y^d)/(x+y)):ℂ) := by
  rw [raw_ray_derivative]
  unfold mixedStencil
  push_cast
  rw [Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  calc
    _ = ((realWeight p r*realWeight q s:ℝ):ℂ)*
        (iteratedDeriv d (nodeRay r s) 0/(d.factorial:ℂ)) := by push_cast; ring
    _ = _ := by rw [node_ray_coefficient]; push_cast; ring

/-- The phase-normalized first correction of the native even source, in
arbitrary order. No pivot sign or finite theta certificate is used. -/
theorem native_first_correction_all_order (i j : ℕ) :
    (-1:ℂ)^(i+j)*
      (iteratedDeriv (2*(i+j+1)+1) (rawRay (2*i) (2*j)) 0 /
        ((2*(i+j+1)+1).factorial:ℂ)) /
      ((2*i).factorial:ℂ) / ((2*j).factorial:ℂ)=
      -(firstRadialCoefficient i j:ℂ)*(canonicalCompletedNativeLogDerivativeMoment (i+j+1):ℂ) := by
  rw [raw_ray_coefficient,readout_coefficient_odd]
  have hc := congrArg (fun x : ℝ => (x:ℂ)) (original_quotient_first_correction i j)
  push_cast at hc
  have hp : (-1:ℂ)^(i+j)*(-1:ℂ)^(i+j+1)= -1 := by
    rw [← pow_add, show i+j+(i+j+1)=2*(i+j)+1 by omega, pow_add, pow_mul]
    norm_num
  calc
    _ = ((-1:ℂ)^(i+j)*(-1:ℂ)^(i+j+1))*
        (mixedStencil (2*i) (2*j) (fun x y =>
          (x^(2*(i+j+1)+1)+y^(2*(i+j+1)+1))/(x+y)):ℂ) /
        ((2*i).factorial:ℂ) / ((2*j).factorial:ℂ)*
        (canonicalCompletedNativeLogDerivativeMoment (i+j+1):ℂ) := by ring
    _ = _ := by rw [hp]; linear_combination - (canonicalCompletedNativeLogDerivativeMoment (i+j+1):ℂ)*hc

/-- Canonical extraction for both even and shifted sectors, arbitrary indices.
The first correction is a signed moment, not a positive new metric. -/
theorem native_same_parity_first_correction (s i j : ℕ) :
    (-1:ℂ)^(i+j)*
      (iteratedDeriv (2*(i+j+s+1)+1) (rawRay (2*i+s) (2*j+s)) 0 /
        ((2*(i+j+s+1)+1).factorial:ℂ)) /
      ((2*i+s).factorial:ℂ) / ((2*j+s).factorial:ℂ)=
      -(parityRadialCoefficient s i j:ℂ)*
        (canonicalCompletedNativeLogDerivativeMoment (i+j+s+1):ℂ) := by
  rw [raw_ray_coefficient,readout_coefficient_odd]
  have hc := congrArg (fun x : ℝ => (x:ℂ)) (original_quotient_same_parity s i j)
  push_cast at hc
  have hp : (-1:ℂ)^(i+j)*(-1:ℂ)^(i+j+s+1)= -(-1:ℂ)^s := by
    rw [← pow_add, show i+j+(i+j+s+1)=2*(i+j)+(s+1) by omega, pow_add, pow_mul, pow_succ]
    norm_num
    rw [pow_succ]
    ring
  calc
    _ = ((-1:ℂ)^(i+j)*(-1:ℂ)^(i+j+s+1))*
        (mixedStencil (2*i+s) (2*j+s) (fun x y =>
          (x^(2*(i+j+s+1)+1)+y^(2*(i+j+s+1)+1))/(x+y)):ℂ) /
        ((2*i+s).factorial:ℂ) / ((2*j+s).factorial:ℂ)*
        (canonicalCompletedNativeLogDerivativeMoment (i+j+s+1):ℂ) := by ring
    _ = _ := by rw [hp]; linear_combination - (canonicalCompletedNativeLogDerivativeMoment (i+j+s+1):ℂ)*hc

/-- Arbitrarily high Taylor truncation of this exact native ray, with an
analytic remainder still present. This is not an order-uniform bound. -/
theorem raw_ray_exact_remainder (p q order : ℕ) :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧ ∀ᶠ z : ℂ in nhds 0,
      rawRay p q z=(∑ d ∈ Finset.range order,
        (iteratedDeriv d (rawRay p q) 0/(d.factorial:ℂ))*z^d)+z^order*R z := by
  obtain ⟨R,ha,he⟩ := (raw_ray_analytic p q).exists_eventuallyEq_sum_add_pow_mul order
  refine ⟨R,ha,?_⟩
  filter_upwards [he] with z hz
  rw [hz]
  simp only [smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro d _
  ring

end
end CarryBinomialGreen
