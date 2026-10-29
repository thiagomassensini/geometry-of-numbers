import IntegratedControl

namespace CarryIntegratedControl
open CarrySelfAdjointOperator CarryAllOrderTail CarryMaterialVariation CarryJetVariationBudget
open CarryMovingRadial CarryBoundaryReconstruction Filter Topology
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- Explicit derivative of a finite native jet combination. -/
def jetCombinationVelocity (N J : ℕ) (orders : Fin J → ℕ) (coeff : Fin J → ℂ)
    (t : ℝ) : Fin N → ℂ := fun i =>
  ∑ j : Fin J, coeff j * (-(orders j:ℂ)/(t:ℂ)*radialJetVector N (orders j) t i)

theorem jet_combination_velocity (N J : ℕ) (orders : Fin J → ℕ) (coeff : Fin J → ℂ)
    (t : ℝ) (ht : t≠0) :
    rawVelocity N (jetCombination N J orders coeff) t = jetCombinationVelocity N J orders coeff t := by
  funext i
  have hd := HasDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
    (radial_jet_hasDerivAt N (orders j) t ht i).const_mul (coeff j))
  exact hd.deriv

theorem jet_combination_continuous (N J : ℕ) (orders : Fin J → ℕ) (coeff : Fin J → ℂ)
    (t : ℝ) (ht : t≠0) (i : Fin N) :
    ContinuousAt (fun h => jetCombination N J orders coeff h i) t := by
  exact (jet_combination_differentiable N J orders coeff t ht i).continuousAt

theorem jet_velocity_continuous (N J : ℕ) (orders : Fin J → ℕ) (coeff : Fin J → ℂ)
    (t : ℝ) (ht : t≠0) (i : Fin N) :
    ContinuousAt (fun h => jetCombinationVelocity N J orders coeff h i) t := by
  have hn : (t:ℂ)≠0 := by exact_mod_cast ht
  have hI : Complex.I*(t:ℂ)≠0 := mul_ne_zero Complex.I_ne_zero hn
  have hc : ContinuousAt (fun h : ℝ => (h:ℂ)) t := Complex.continuous_ofReal.continuousAt
  have hj (j : Fin J) : ContinuousAt (fun h : ℝ => coeff j *
      (-(orders j:ℂ)/(h:ℂ)*radialJetVector N (orders j) h i)) t := by
    unfold radialJetVector
    have hden : ((orders j).factorial:ℂ)*(Complex.I*(t:ℂ))^(orders j) ≠ 0 :=
      mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)) (pow_ne_zero _ hI)
    have hb : ContinuousAt (fun h : ℝ => ((orders j).factorial:ℂ)*
        (Complex.I*(h:ℂ))^(orders j)) t :=
      continuousAt_const.mul ((continuousAt_const.mul hc).pow (orders j))
    exact continuousAt_const.mul ((continuousAt_const.div hc hn).mul
      ((hb.inv₀ hden).mul continuousAt_const))
  change Tendsto (fun h : ℝ => ∑ j : Fin J, coeff j *
      (-(orders j:ℂ)/(h:ℂ)*radialJetVector N (orders j) h i)) (nhds t) _
  simpa only [ContinuousAt,jetCombinationVelocity] using tendsto_finsetSum (Finset.univ : Finset (Fin J)) (fun j _ => hj j)

theorem address_budget_continuous (i M : ℕ) (t : ℝ) (ht : ‖point t i‖<1/4) :
    ContinuousAt (fun h => addressBudget h i M) t := by
  have hn : 1-(22/175:ℝ)*‖point t i‖^2 ≠ 0 := by
    have hp : 0 < 1-(22/175:ℝ)*‖point t i‖^2 := by nlinarith [norm_nonneg (point t i)]
    exact ne_of_gt hp
  have hc : ContinuousAt (fun h : ℝ => (h:ℂ)) t := Complex.continuous_ofReal.continuousAt
  unfold addressBudget point at *
  fun_prop (disch := assumption)

theorem family_budget_continuous (N M : ℕ) (t : ℝ) (ht : (N:ℝ)*|t|<1/4) :
    ContinuousAt (fun h => familyBudget N M h) t := by
  unfold familyBudget
  change Tendsto (fun h => ∑ i : Fin N, addressBudget h i M) (nhds t) _
  simpa only [ContinuousAt] using tendsto_finsetSum (Finset.univ : Finset (Fin N))
    (fun i _ => address_budget_continuous i M t (finite_grid_radius N t ht i))

theorem velocity_budget_continuous (N M : ℕ) (t : ℝ) :
    ContinuousAt (fun h => velocityFamilyBudget N M h) t := by
  unfold velocityFamilyBudget velocityAddressBudget point
  fun_prop


theorem size_continuous (N : ℕ) (x : ℝ → Fin N → ℂ) (t : ℝ)
    (hx : ∀ i, ContinuousAt (fun h => x h i) t) :
    ContinuousAt (fun h => size N (x h)) t := by
  unfold size
  change Tendsto (fun h => ∑ i : Fin N, ‖x h i‖) (nhds t) _
  simpa only [ContinuousAt] using tendsto_finsetSum (Finset.univ : Finset (Fin N))
    (fun i _ => (hx i).norm)

def explicitJetBudget (N M J K : ℕ) (ordersX : Fin J → ℕ) (ordersY : Fin K → ℕ)
    (coeffX : Fin J → ℂ) (coeffY : Fin K → ℂ) (t : ℝ) : ℝ :=
  ‖(2/(t:ℂ))‖ *
    (familyBudget N M t*size N (jetCombinationVelocity N J ordersX coeffX t)*
        size N (jetCombination N K ordersY coeffY t) +
     familyBudget N M t*size N (jetCombination N J ordersX coeffX t)*
        size N (jetCombinationVelocity N K ordersY coeffY t)) +
  ‖(2/(t:ℂ)^2)‖ * ((|t| *velocityFamilyBudget N M t+familyBudget N M t)*
    size N (jetCombination N J ordersX coeffX t)*size N (jetCombination N K ordersY coeffY t))

theorem explicit_jet_budget_eq (N M J K : ℕ) (ordersX : Fin J → ℕ) (ordersY : Fin K → ℕ)
    (coeffX : Fin J → ℂ) (coeffY : Fin K → ℂ) (t : ℝ) (ht : t≠0) :
    pointBudget N M (jetCombination N J ordersX coeffX) (jetCombination N K ordersY coeffY) t =
      explicitJetBudget N M J K ordersX ordersY coeffX coeffY t := by
  unfold pointBudget explicitJetBudget
  rw [jet_combination_velocity N J ordersX coeffX t ht,
    jet_combination_velocity N K ordersY coeffY t ht]

theorem explicit_jet_budget_continuous (N M J K : ℕ)
    (ordersX : Fin J → ℕ) (ordersY : Fin K → ℕ) (coeffX : Fin J → ℂ) (coeffY : Fin K → ℂ)
    (t : ℝ) (ht : t≠0) (hh : (N:ℝ)*|t| < 1/4) :
    ContinuousAt (explicitJetBudget N M J K ordersX ordersY coeffX coeffY) t := by
  have hx := size_continuous N (jetCombination N J ordersX coeffX) t
    (jet_combination_continuous N J ordersX coeffX t ht)
  have hy := size_continuous N (jetCombination N K ordersY coeffY) t
    (jet_combination_continuous N K ordersY coeffY t ht)
  have hvx := size_continuous N (jetCombinationVelocity N J ordersX coeffX) t
    (jet_velocity_continuous N J ordersX coeffX t ht)
  have hvy := size_continuous N (jetCombinationVelocity N K ordersY coeffY) t
    (jet_velocity_continuous N K ordersY coeffY t ht)
  have he := family_budget_continuous N M t hh
  have hv := velocity_budget_continuous N M t
  have hc : ContinuousAt (fun h : ℝ => (h:ℂ)) t := Complex.continuous_ofReal.continuousAt
  have hn : (t:ℂ)≠0 := by exact_mod_cast ht
  have h1 : ContinuousAt (fun h : ℝ => ‖(2/(h:ℂ))‖) t := (continuousAt_const.div hc hn).norm
  have h2 : ContinuousAt (fun h : ℝ => ‖(2/(h:ℂ)^2)‖) t :=
    (continuousAt_const.div (hc.pow 2) (pow_ne_zero 2 hn)).norm
  have ha : ContinuousAt (fun h : ℝ => |h|) t := continuousAt_id.norm
  unfold explicitJetBudget
  exact (h1.mul (((he.mul hvx).mul hy).add ((he.mul hx).mul hvy))).add
    (h2.mul ((((ha.mul hv).add he).mul hx).mul hy))

theorem point_jet_budget_continuous (N M J K : ℕ)
    (ordersX : Fin J → ℕ) (ordersY : Fin K → ℕ) (coeffX : Fin J → ℂ) (coeffY : Fin K → ℂ)
    (t : ℝ) (ht : t≠0) (hh : (N:ℝ)*|t| < 1/4) :
    ContinuousAt (pointBudget N M (jetCombination N J ordersX coeffX)
      (jetCombination N K ordersY coeffY)) t := by
  have he : pointBudget N M (jetCombination N J ordersX coeffX) (jetCombination N K ordersY coeffY) =ᶠ[nhds t]
      explicitJetBudget N M J K ordersX ordersY coeffX coeffY := by
    filter_upwards [continuousAt_id.eventually_ne ht] with h hn
    exact explicit_jet_budget_eq N M J K ordersX ordersY coeffX coeffY h hn
  exact (explicit_jet_budget_continuous N M J K ordersX ordersY coeffX coeffY t ht hh).congr_of_eventuallyEq he

theorem native_jet_budget_interval_integrable (N M J K : ℕ)
    (ordersX : Fin J → ℕ) (ordersY : Fin K → ℕ) (coeffX : Fin J → ℂ) (coeffY : Fin K → ℂ)
    (a b : ℝ) (hab : a≤b) (ha : 0<a) (hb : (N:ℝ)*b < 1/4) :
    IntervalIntegrable (pointBudget N M (jetCombination N J ordersX coeffX)
      (jetCombination N K ordersY coeffY)) MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le hab]
  intro t ht
  have hp : 0<t := lt_of_lt_of_le ha ht.1
  have hh : (N:ℝ)*|t|<1/4 := by
    rw [abs_of_pos hp]
    have hh := mul_le_mul_of_nonneg_left ht.2 (show (0:ℝ) ≤ N by positivity)
    linarith
  exact (point_jet_budget_continuous N M J K ordersX ordersY coeffX coeffY t hp.ne' hh).continuousWithinAt

/-- Integrated full-source tail between adjacent native steps, with all
analytic and integrability gates discharged for every finite jet combination. -/
theorem integrated_native_grid_jets_unconditional (N M J K k : ℕ)
    (ordersX : Fin J → ℕ) (ordersY : Fin K → ℕ)
    (coeffX : Fin J → ℂ) (coeffY : Fin K → ℂ)
    (hk : (N:ℝ)*radialFourSourceStep k < 1/4) :
    ‖(physicalCurve N (jetCombination N J ordersX coeffX) (jetCombination N K ordersY coeffY) (radialFourSourceStep k)-
       prefixCurve N M (jetCombination N J ordersX coeffX) (jetCombination N K ordersY coeffY) (radialFourSourceStep k)) -
      (physicalCurve N (jetCombination N J ordersX coeffX) (jetCombination N K ordersY coeffY) (radialFourSourceStep (k+1))-
       prefixCurve N M (jetCombination N J ordersX coeffX) (jetCombination N K ordersY coeffY) (radialFourSourceStep (k+1)))‖ ≤
      ∫ t in (radialFourSourceStep (k+1))..(radialFourSourceStep k),
        pointBudget N M (jetCombination N J ordersX coeffX) (jetCombination N K ordersY coeffY) t := by
  apply integrated_native_grid_jets N M J K k ordersX ordersY coeffX coeffY hk
  exact native_jet_budget_interval_integrable N M J K ordersX ordersY coeffX coeffY
    (radialFourSourceStep (k+1)) (radialFourSourceStep k) (radial_step_decreasing k).le
    (radial_step_positive (k+1)) hk

end
end CarryIntegratedControl
