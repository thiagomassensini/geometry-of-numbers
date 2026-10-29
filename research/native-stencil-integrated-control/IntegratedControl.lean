import FiniteVelocityBudget
import SquaredStepBudget
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace CarryIntegratedControl
open CarrySelfAdjointOperator CarryAllOrderTail CarryMaterialVariation CarryJetVariationBudget
open CarryMovingRadial CarryBoundaryReconstruction Filter Topology
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

def physicalCurve (N : ℕ) (x y : ℝ → Fin N → ℂ) (t : ℝ) : ℂ :=
  2*canonicalCompletedNativeProjectiveChiralForm (curveState N t (x t)) (curveState N t (y t))

def prefixCurve (N M : ℕ) (x y : ℝ → Fin N → ℂ) (t : ℝ) : ℂ :=
  (2/(t:ℂ))*materialPair N (fun i => rhoPrefix t i M) (x t) (y t)

def pointBudget (N M : ℕ) (x y : ℝ → Fin N → ℂ) (t : ℝ) : ℝ :=
  ‖(2/(t:ℂ))‖ *
    (familyBudget N M t*size N (rawVelocity N x t)*size N (y t) +
     familyBudget N M t*size N (x t)*size N (rawVelocity N y t)) +
  ‖(2/(t:ℂ)^2)‖ *
    ((|t| *velocityFamilyBudget N M t+familyBudget N M t)*size N (x t)*size N (y t))

/-- The prior equality of full physical synthesis is differentiated locally;
no component of the two-leg state is dropped. -/
theorem physical_curve_hasDerivAt (N : ℕ) (x y : ℝ → Fin N → ℂ) (t : ℝ)
    (ht : 0<t) (hh : (N:ℝ)*|t| < 1/4)
    (hx : ∀ i, DifferentiableAt ℝ (fun h => x h i) t)
    (hy : ∀ i, DifferentiableAt ℝ (fun h => y h i) t) :
    HasDerivAt (physicalCurve N x y)
      (materialVariation N t (fun i => rho t i) (rhoVelocity N t)
        (x t) (rawVelocity N x t) (y t) (rawVelocity N y t)) t := by
  have hz (i : Fin N) := finite_grid_radius N t hh i
  have hD (i : Fin N) := CarryEffectiveRadial.quarter_disc_in_domain (point t i) (hz i)
  have hF (i : Fin N) := (finite_radial_regular N t hh i).1
  have hP (i : Fin N) := (finite_radial_regular N t hh i).2
  have he : physicalCurve N x y =ᶠ[nhds t] fun h => responsePair N h (x h) (y h) := by
    filter_upwards [source_regular_local N t hD hF hP,lt_mem_nhds ht] with h hr hp
    exact (curve_full_pair N h _ _).trans (fullPair_eq_response N h hp.le _ _
      (fun i => (hr i).2.1) (fun i => (hr i).2.2))
  have hd := scaled_material_hasDerivAt N (fun h i => rho h i) x y
    (rhoVelocity N t) (rawVelocity N x t) (rawVelocity N y t) t ht.ne'
    (fun i => (rho_differentiable t i (hD i) (hF i)).hasDerivAt)
    (fun i => (hx i).hasDerivAt) (fun i => (hy i).hasDerivAt)
  exact hd.congr_of_eventuallyEq he

theorem prefix_curve_hasDerivAt (N M : ℕ) (x y : ℝ → Fin N → ℂ) (t : ℝ)
    (ht : t≠0)
    (hx : ∀ i, DifferentiableAt ℝ (fun h => x h i) t)
    (hy : ∀ i, DifferentiableAt ℝ (fun h => y h i) t) :
    HasDerivAt (prefixCurve N M x y)
      (materialVariation N t (fun i => rhoPrefix t i M) (velocityPrefix N M t)
        (x t) (rawVelocity N x t) (y t) (rawVelocity N y t)) t := by
  have hp (i : Fin N) : DifferentiableAt ℝ (fun h : ℝ => rhoPrefix h i M) t := by
    unfold rhoPrefix point
    fun_prop
  exact scaled_material_hasDerivAt N (fun h i => rhoPrefix h i M) x y
    (velocityPrefix N M t) (rawVelocity N x t) (rawVelocity N y t) t ht
    (fun i => (hp i).hasDerivAt) (fun i => (hx i).hasDerivAt) (fun i => (hy i).hasDerivAt)

/-- Pointwise bound for the derivative of the *full source minus its
same-source prefix*, including input velocities and every ordered crossing. -/
theorem source_error_hasDerivAt_and_bound (N M : ℕ) (x y : ℝ → Fin N → ℂ) (t : ℝ)
    (ht : 0<t) (hh : (N:ℝ)*|t| < 1/4)
    (hx : ∀ i, DifferentiableAt ℝ (fun h => x h i) t)
    (hy : ∀ i, DifferentiableAt ℝ (fun h => y h i) t) :
    ∃ v : ℂ, HasDerivAt (fun h => physicalCurve N x y h-prefixCurve N M x y h) v t ∧
      ‖v‖ ≤ pointBudget N M x y t := by
  have hp := physical_curve_hasDerivAt N x y t ht hh hx hy
  have hq := prefix_curve_hasDerivAt N M x y t ht.ne' hx hy
  refine ⟨_, hp.sub hq, ?_⟩
  have he := physical_derivative_explicit_budget N M x y t ht hh hx hy
  change ‖deriv (physicalCurve N x y) t - _‖ ≤ _ at he
  rw [hp.deriv] at he
  exact he

/-- Integrate the actual source error between two positive radial scales.
The primitive W bounds the explicit point budget on the interval; supplying
such a primitive does not assert positivity of the critical residual. -/
theorem integrated_source_error (N M : ℕ) (x y : ℝ → Fin N → ℂ)
    (a b : ℝ) (hab : a≤b) (W W' : ℝ → ℝ)
    (hregular : ∀ t ∈ Set.Icc a b, 0<t ∧ (N:ℝ)*|t|<1/4)
    (hx : ∀ t ∈ Set.Icc a b, ∀ i, DifferentiableAt ℝ (fun h => x h i) t)
    (hy : ∀ t ∈ Set.Icc a b, ∀ i, DifferentiableAt ℝ (fun h => y h i) t)
    (hW : ∀ t ∈ Set.Icc a b, HasDerivAt W (W' t) t)
    (hbudget : ∀ t ∈ Set.Icc a b, pointBudget N M x y t ≤ W' t) :
    ‖(physicalCurve N x y b-prefixCurve N M x y b) -
      (physicalCurve N x y a-prefixCurve N M x y a)‖ ≤ W b-W a := by
  let e : ℝ → ℂ := fun t => physicalCurve N x y t-prefixCurve N M x y t
  have he (t : ℝ) (ht : t ∈ Set.Icc a b) :=
    source_error_hasDerivAt_and_bound N M x y t (hregular t ht).1 (hregular t ht).2 (hx t ht) (hy t ht)
  let v : ℝ → ℂ := fun t => deriv e t
  have hv (t : ℝ) (ht : t ∈ Set.Icc a b) : HasDerivAt e (v t) t ∧ ‖v t‖ ≤ W' t := by
    obtain ⟨z,hz,hbound⟩ := he t ht
    have hval : v t=z := hz.deriv
    rw [hval]
    exact ⟨hz,hbound.trans (hbudget t ht)⟩
  have hcont : ContinuousOn (fun t => e t-e a) (Set.Icc a b) := by
    intro t ht
    exact ((hv t ht).1.sub_const (e a)).continuousAt.continuousWithinAt
  have hv' : ∀ t ∈ Set.Ico a b, HasDerivWithinAt (fun t => e t-e a) (v t) (Set.Ici t) t := by
    intro t ht
    exact ((hv t (Set.Ico_subset_Icc_self ht)).1.sub_const (e a)).hasDerivWithinAt
  have hwcont : ContinuousOn (fun t => W t-W a) (Set.Icc a b) := by
    intro t ht
    exact ((hW t ht).sub_const (W a)).continuousAt.continuousWithinAt
  have hw' : ∀ t ∈ Set.Ico a b, HasDerivWithinAt (fun t => W t-W a) (W' t) (Set.Ici t) t := by
    intro t ht
    exact ((hW t (Set.Ico_subset_Icc_self ht)).sub_const (W a)).hasDerivWithinAt
  have hb : ∀ t ∈ Set.Ico a b, ‖v t‖ ≤ W' t := by
    intro t ht
    exact (hv t (Set.Ico_subset_Icc_self ht)).2
  have h := image_norm_le_of_norm_deriv_right_le_deriv_boundary' hcont hv'
    (by simp) hwcont hw' hb (Set.right_mem_Icc.mpr hab)
  exact h


/-- A finite combination of the literal original jets, with independent
complex coefficients and orders. Critical combinations are included without
assuming a sign of their associated residual. -/
def jetCombination (N J : ℕ) (orders : Fin J → ℕ) (coeff : Fin J → ℂ)
    (t : ℝ) : Fin N → ℂ := fun i =>
  ∑ j : Fin J, coeff j * radialJetVector N (orders j) t i

theorem jet_combination_differentiable (N J : ℕ) (orders : Fin J → ℕ)
    (coeff : Fin J → ℂ) (t : ℝ) (ht : t≠0) (i : Fin N) :
    DifferentiableAt ℝ (fun h => jetCombination N J orders coeff h i) t := by
  have hd := HasDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
    (radial_jet_hasDerivAt N (orders j) t ht i).const_mul (coeff j))
  exact hd.differentiableAt

/-- Integrated tail control for arbitrary two independent combinations of
original jets, including critical combinations. W is a concrete remaining
majorant obligation, not an assumption of positivity. -/
theorem integrated_original_jet_combinations (N M J K : ℕ)
    (ordersX : Fin J → ℕ) (ordersY : Fin K → ℕ)
    (coeffX : Fin J → ℂ) (coeffY : Fin K → ℂ)
    (a b : ℝ) (hab : a≤b) (W W' : ℝ → ℝ)
    (hregular : ∀ t ∈ Set.Icc a b, 0<t ∧ (N:ℝ)*|t|<1/4)
    (hW : ∀ t ∈ Set.Icc a b, HasDerivAt W (W' t) t)
    (hbudget : ∀ t ∈ Set.Icc a b,
      pointBudget N M (jetCombination N J ordersX coeffX) (jetCombination N K ordersY coeffY) t ≤ W' t) :
    ‖(physicalCurve N (jetCombination N J ordersX coeffX) (jetCombination N K ordersY coeffY) b-
       prefixCurve N M (jetCombination N J ordersX coeffX) (jetCombination N K ordersY coeffY) b) -
      (physicalCurve N (jetCombination N J ordersX coeffX) (jetCombination N K ordersY coeffY) a-
       prefixCurve N M (jetCombination N J ordersX coeffX) (jetCombination N K ordersY coeffY) a)‖ ≤ W b-W a := by
  apply integrated_source_error N M (jetCombination N J ordersX coeffX)
    (jetCombination N K ordersY coeffY) a b hab W W' hregular
  · intro t ht i
    exact jet_combination_differentiable N J ordersX coeffX t (hregular t ht).1.ne' i
  · intro t ht i
    exact jet_combination_differentiable N K ordersY coeffY t (hregular t ht).1.ne' i
  · exact hW
  · exact hbudget


/-- Exact transport to the completed source before discarding anything: the
finite prefix and its full residual retain both independent inputs and all
ordered Cauchy crosses. -/
theorem physical_curve_exact_prefix_and_tail (N M : ℕ) (x y : ℝ → Fin N → ℂ)
    (t : ℝ) (ht : 0<t) (hh : (N:ℝ)*|t| < 1/4) :
    physicalCurve N x y t = prefixCurve N M x y t +
      (2/(t:ℂ))*materialPair N (fun i => rho t i-rhoPrefix t i M) (x t) (y t) := by
  have hF (i : Fin N) := (finite_radial_regular N t hh i).1
  have hP (i : Fin N) := (finite_radial_regular N t hh i).2
  have hp := (curve_full_pair N t (x t) (y t)).trans
    (fullPair_eq_response N t (le_of_lt ht) (x t) (y t) hF hP)
  have he := materialPair_affine N (fun i => rhoPrefix t i M) (fun i => rho t i) (x t) (y t) 1
  simp only [one_mul] at he
  unfold physicalCurve prefixCurve
  rw [hp]
  change (2/(t:ℂ))*materialPair N (fun i => rho t i) (x t) (y t) = _
  rw [he]
  ring


/-- Literal integral of the explicit physical derivative-error budget.
Integrability hypotheses are explicit and do not encode a sign assumption. -/
theorem integrated_source_error_integral (N M : ℕ) (x y : ℝ → Fin N → ℂ)
    (a b : ℝ) (hab : a≤b)
    (hregular : ∀ t ∈ Set.Icc a b, 0<t ∧ (N:ℝ)*|t|<1/4)
    (hx : ∀ t ∈ Set.Icc a b, ∀ i, DifferentiableAt ℝ (fun h => x h i) t)
    (hy : ∀ t ∈ Set.Icc a b, ∀ i, DifferentiableAt ℝ (fun h => y h i) t)
    (hBint : IntervalIntegrable (pointBudget N M x y) MeasureTheory.volume a b) :
    ‖(physicalCurve N x y b-prefixCurve N M x y b) -
      (physicalCurve N x y a-prefixCurve N M x y a)‖ ≤
      ∫ t in a..b, pointBudget N M x y t := by
  let e : ℝ → ℂ := fun t => physicalCurve N x y t-prefixCurve N M x y t
  have hv (t : ℝ) (ht : t ∈ Set.Icc a b) :
      HasDerivAt e (deriv e t) t ∧ ‖deriv e t‖ ≤ pointBudget N M x y t := by
    obtain ⟨z,hz,hbound⟩ := source_error_hasDerivAt_and_bound N M x y t
      (hregular t ht).1 (hregular t ht).2 (hx t ht) (hy t ht)
    have heq : deriv e t=z := hz.deriv
    rw [heq]
    exact ⟨hz,hbound⟩
  have hDint : IntervalIntegrable (deriv e) MeasureTheory.volume a b := by
    apply hBint.mono_fun' (aestronglyMeasurable_deriv e _)
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with t ht
    have ht' : t ∈ Set.Ioc a b := by simpa [Set.uIoc_of_le hab] using ht
    exact (hv t ⟨ht'.1.le,ht'.2⟩).2
  have heq : (∫ t in a..b, deriv e t) = e b-e a := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t ht
      exact (hv t (by simpa [Set.uIcc_of_le hab] using ht)).1
    · exact hDint
  change ‖e b-e a‖ ≤ _
  rw [← heq]
  apply intervalIntegral.norm_integral_le_of_norm_le hab _ hBint
  filter_upwards [] with t ht
  exact (hv t ⟨ht.1.le,ht.2⟩).2

/-- Integral control for arbitrary pairs of finite combinations of literal
native jets, including fixed critical directions of any finite order. -/
theorem integrated_original_jets_integral (N M J K : ℕ)
    (ordersX : Fin J → ℕ) (ordersY : Fin K → ℕ)
    (coeffX : Fin J → ℂ) (coeffY : Fin K → ℂ)
    (a b : ℝ) (hab : a≤b)
    (hregular : ∀ t ∈ Set.Icc a b, 0<t ∧ (N:ℝ)*|t|<1/4)
    (hBint : IntervalIntegrable (pointBudget N M (jetCombination N J ordersX coeffX)
      (jetCombination N K ordersY coeffY)) MeasureTheory.volume a b) :
    ‖(physicalCurve N (jetCombination N J ordersX coeffX) (jetCombination N K ordersY coeffY) b-
       prefixCurve N M (jetCombination N J ordersX coeffX) (jetCombination N K ordersY coeffY) b) -
      (physicalCurve N (jetCombination N J ordersX coeffX) (jetCombination N K ordersY coeffY) a-
       prefixCurve N M (jetCombination N J ordersX coeffX) (jetCombination N K ordersY coeffY) a)‖ ≤
      ∫ t in a..b, pointBudget N M (jetCombination N J ordersX coeffX) (jetCombination N K ordersY coeffY) t := by
  apply integrated_source_error_integral N M (jetCombination N J ordersX coeffX)
    (jetCombination N K ordersY coeffY) a b hab hregular
  · intro t ht i
    exact jet_combination_differentiable N J ordersX coeffX t (hregular t ht).1.ne' i
  · intro t ht i
    exact jet_combination_differentiable N K ordersY coeffY t (hregular t ht).1.ne' i
  · exact hBint


/-- Actual adjacent native radial steps, for arbitrary finite combinations
of original jets and their full polarized source. -/
theorem integrated_native_grid_jets (N M J K k : ℕ)
    (ordersX : Fin J → ℕ) (ordersY : Fin K → ℕ)
    (coeffX : Fin J → ℂ) (coeffY : Fin K → ℂ)
    (hk : (N:ℝ)*radialFourSourceStep k < 1/4)
    (hBint : IntervalIntegrable (pointBudget N M (jetCombination N J ordersX coeffX)
      (jetCombination N K ordersY coeffY)) MeasureTheory.volume
        (radialFourSourceStep (k+1)) (radialFourSourceStep k)) :
    ‖(physicalCurve N (jetCombination N J ordersX coeffX) (jetCombination N K ordersY coeffY) (radialFourSourceStep k)-
       prefixCurve N M (jetCombination N J ordersX coeffX) (jetCombination N K ordersY coeffY) (radialFourSourceStep k)) -
      (physicalCurve N (jetCombination N J ordersX coeffX) (jetCombination N K ordersY coeffY) (radialFourSourceStep (k+1))-
       prefixCurve N M (jetCombination N J ordersX coeffX) (jetCombination N K ordersY coeffY) (radialFourSourceStep (k+1)))‖ ≤
      ∫ t in (radialFourSourceStep (k+1))..(radialFourSourceStep k),
        pointBudget N M (jetCombination N J ordersX coeffX) (jetCombination N K ordersY coeffY) t := by
  have hstep := radial_step_decreasing k
  apply integrated_original_jets_integral N M J K ordersX ordersY coeffX coeffY
    (radialFourSourceStep (k+1)) (radialFourSourceStep k) hstep.le
  · intro t ht
    have hpos : 0<t := lt_of_lt_of_le (radial_step_positive (k+1)) ht.1
    refine ⟨hpos,?_⟩
    rw [abs_of_pos hpos]
    have hb := mul_le_mul_of_nonneg_left ht.2 (show (0:ℝ)≤N by positivity)
    linarith
  · exact hBint

end
end CarryIntegratedControl
