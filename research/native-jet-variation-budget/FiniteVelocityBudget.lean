import RemainderVelocity
import JetEulerVariation

namespace CarryJetVariationBudget
open CarrySelfAdjointOperator CarryAllOrderTail CarryMaterialVariation
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

def velocityPrefix (N M : ℕ) (t : ℝ) : Fin N → ℂ :=
  fun i => deriv (fun h : ℝ => rhoPrefix h i M) t

def velocityAddressBudget (M i : ℕ) (t : ℝ) : ℝ :=
  (((i:ℝ)+1)/2) *
    (((2*M+1:ℕ):ℝ)*‖CarryMovingRadial.point t i‖^(2*M) +
       4*‖CarryMovingRadial.point t i‖^(2*M+1))

def velocityFamilyBudget (N M : ℕ) (t : ℝ) : ℝ :=
  ∑ i : Fin N, velocityAddressBudget M i t

theorem velocity_address_budget_nonneg (M i : ℕ) (t : ℝ) :
    0 ≤ velocityAddressBudget M i t := by
  unfold velocityAddressBudget
  positivity

theorem native_velocity_address_error (M i : ℕ) (t : ℝ)
    (hz : ‖CarryMovingRadial.point t i‖ < 1/4)
    (hD : CarryMovingRadial.point t i ∈ completedNativeHeightDomain)
    (hF : completedNativeOperatorCharacteristic (CarryMovingRadial.point t i) ≠ 0) :
    ‖deriv (fun h : ℝ => CarryMovingRadial.rho h i) t -
      deriv (fun h : ℝ => rhoPrefix h i M) t‖ ≤ velocityAddressBudget M i t := by
  have hr := rho_differentiable t i hD hF
  have hp : DifferentiableAt ℝ (fun h : ℝ => rhoPrefix h i M) t := by
    unfold rhoPrefix CarryMovingRadial.point
    fun_prop
  have he := radial_response_derivative_prefix_error M i t hz hD hF
  change ‖deriv ((fun h : ℝ => CarryMovingRadial.rho h i) -
    (fun h : ℝ => rhoPrefix h i M)) t‖ ≤ _ at he
  rw [deriv_sub hr hp] at he
  exact he

/-- Fully explicit finite-family error for the derivative of the completed
physical source, including response and both moving input derivatives. -/
theorem physical_derivative_explicit_budget (N M : ℕ) (x y : ℝ → Fin N → ℂ) (t : ℝ)
    (ht : 0 < t) (hh : (N:ℝ)*|t| < 1/4)
    (hx : ∀ i, DifferentiableAt ℝ (fun h => x h i) t)
    (hy : ∀ i, DifferentiableAt ℝ (fun h => y h i) t) :
    ‖deriv (fun h => 2*canonicalCompletedNativeProjectiveChiralForm
        (CarryMovingRadial.curveState N h (x h)) (CarryMovingRadial.curveState N h (y h))) t -
      materialVariation N t (fun i => rhoPrefix t i M) (velocityPrefix N M t)
        (x t) (rawVelocity N x t) (y t) (rawVelocity N y t)‖ ≤
      ‖(2/(t:ℂ))‖ * (familyBudget N M t*size N (rawVelocity N x t)*size N (y t) +
        familyBudget N M t*size N (x t)*size N (rawVelocity N y t)) +
      ‖(2/(t:ℂ)^2)‖ * ((|t| *velocityFamilyBudget N M t+familyBudget N M t)*size N (x t)*size N (y t)) := by
  have hz (i : Fin N) := finite_grid_radius N t hh i
  have hD (i : Fin N) := CarryEffectiveRadial.quarter_disc_in_domain (CarryMovingRadial.point t i) (hz i)
  have hF (i : Fin N) := (finite_radial_regular N t hh i).1
  have hP (i : Fin N) := (finite_radial_regular N t hh i).2
  have he (i : Fin N) : 0 ≤ addressBudget t i M := address_budget_nonneg t i M (hz i)
  have hv (i : Fin N) : 0 ≤ velocityAddressBudget M i t := velocity_address_budget_nonneg M i t
  apply physical_derivative_approximation N x y t (fun i => rhoPrefix t i M)
    (velocityPrefix N M t) (familyBudget N M t) (velocityFamilyBudget N M t)
    ht hx hy hD hF hP
  · exact Finset.sum_nonneg (fun i _ => he i)
  · exact Finset.sum_nonneg (fun i _ => hv i)
  · intro i
    exact (native_address_prefix_error t i M (hz i) (hF i)).trans
      (Finset.single_le_sum (fun j _ => he j) (Finset.mem_univ i))
  · intro i
    exact (native_velocity_address_error M i t (hz i) (hD i) (hF i)).trans
      (Finset.single_le_sum (fun j _ => hv j) (Finset.mem_univ i))


/-- Specialization to the literal factorial-normalized native jet stencils,
with their original t-dependent amplitudes. If m,n<N, the existing
radial_jet_curve_complete_jet theorem identifies both with the full original
physical jets on the native grid. -/
theorem native_jets_derivative_explicit_budget (N M m n : ℕ) (t : ℝ)
    (ht : 0 < t) (hh : (N:ℝ)*|t| < 1/4) :
    ‖deriv (fun h => 2*canonicalCompletedNativeProjectiveChiralForm
        (CarryMovingRadial.curveState N h (radialJetVector N m h))
        (CarryMovingRadial.curveState N h (radialJetVector N n h))) t -
      materialVariation N t (fun i => rhoPrefix t i M) (velocityPrefix N M t)
        (radialJetVector N m t) (rawVelocity N (radialJetVector N m) t)
        (radialJetVector N n t) (rawVelocity N (radialJetVector N n) t)‖ ≤
      ‖(2/(t:ℂ))‖ *
        (familyBudget N M t*size N (rawVelocity N (radialJetVector N m) t)*size N (radialJetVector N n t) +
         familyBudget N M t*size N (radialJetVector N m t)*size N (rawVelocity N (radialJetVector N n) t)) +
      ‖(2/(t:ℂ)^2)‖ * ((|t| *velocityFamilyBudget N M t+familyBudget N M t)*
        size N (radialJetVector N m t)*size N (radialJetVector N n t)) := by
  apply physical_derivative_explicit_budget N M (radialJetVector N m) (radialJetVector N n) t ht hh
  · intro i
    exact (radial_jet_hasDerivAt N m t ht.ne' i).differentiableAt
  · intro i
    exact (radial_jet_hasDerivAt N n t ht.ne' i).differentiableAt


/-- The velocity size of a literal jet is explicit in its own order and the
original radial step; it is not uniformly bounded as t approaches zero. -/
theorem native_jet_velocity_size (N m : ℕ) (t : ℝ) (ht : t ≠ 0) :
    size N (rawVelocity N (radialJetVector N m) t) =
      ((m:ℝ)/|t|)*size N (radialJetVector N m t) := by
  have he : rawVelocity N (radialJetVector N m) t =
      fun i => -(m:ℂ)/(t:ℂ)*radialJetVector N m t i := by
    funext i
    exact (radial_jet_hasDerivAt N m t ht i).deriv
  rw [he]
  unfold size
  simp only [norm_mul,norm_div,norm_neg,norm_natCast,Complex.norm_real,Real.norm_eq_abs,
    Finset.mul_sum]


/-- Fully explicit original-jet bound with the exact order-dependent
velocity factors m/t and n/t exposed. -/
theorem native_jets_ordered_velocity_budget (N M m n : ℕ) (t : ℝ)
    (ht : 0 < t) (hh : (N:ℝ)*|t| < 1/4) :
    ‖deriv (fun h => 2*canonicalCompletedNativeProjectiveChiralForm
        (CarryMovingRadial.curveState N h (radialJetVector N m h))
        (CarryMovingRadial.curveState N h (radialJetVector N n h))) t -
      materialVariation N t (fun i => rhoPrefix t i M) (velocityPrefix N M t)
        (radialJetVector N m t) (rawVelocity N (radialJetVector N m) t)
        (radialJetVector N n t) (rawVelocity N (radialJetVector N n) t)‖ ≤
      ‖(2/(t:ℂ))‖ *
        (familyBudget N M t*((m:ℝ)/t*size N (radialJetVector N m t))*size N (radialJetVector N n t) +
         familyBudget N M t*size N (radialJetVector N m t)*((n:ℝ)/t*size N (radialJetVector N n t))) +
      ‖(2/(t:ℂ)^2)‖ * ((|t| *velocityFamilyBudget N M t+familyBudget N M t)*
        size N (radialJetVector N m t)*size N (radialJetVector N n t)) := by
  have h := native_jets_derivative_explicit_budget N M m n t ht hh
  rw [native_jet_velocity_size N m t ht.ne', native_jet_velocity_size N n t ht.ne', abs_of_pos ht] at h
  simpa only [abs_of_pos ht] using h

end
end CarryJetVariationBudget
