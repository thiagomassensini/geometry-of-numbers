import RepartitionBudget

namespace CarryUniformSource
open CarrySourceBezout Filter Topology
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 8000000

theorem responseCoefficient_bound_order (c : ℕ → ℂ) (b : Bool) (L : ℕ) (C : ℝ)
    (hC : 0 ≤ C) (hc : ∀ k ≤ L, ‖c k‖ ≤ C) (n : ℕ) (hn : n+1 ≤ L) :
    ‖responseCoefficient c b n‖ ≤ (L:ℝ)*C := by
  have hcast : ((n+1:ℕ):ℝ) ≤ (L:ℝ) := by exact_mod_cast hn
  cases b with
  | false =>
    cases n with
    | zero =>
      rw [responseCoefficient_even_zero,norm_zero]
      positivity
    | succ n =>
      rw [responseCoefficient_even_succ,norm_mul]
      simp only [norm_neg,Complex.norm_natCast]
      exact mul_le_mul (by exact_mod_cast (show n+1 ≤ L by omega)) (hc (n+1) (by omega)) (norm_nonneg _) (by positivity)
  | true =>
    rw [responseCoefficient_odd,norm_mul]
    simp only [norm_neg,Complex.norm_natCast]
    exact mul_le_mul hcast (hc (n+1) hn) (norm_nonneg _) (by positivity)

theorem coefficientBudget_bound_order (c d : ℕ → ℂ) (b : Bool) (r : ℕ) (C D : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hc : ∀ k ≤ 2*r, ‖c k‖ ≤ C) (hd : ∀ k ≤ 2*r, ‖d k‖ ≤ D)
    (i j : Fin r) : coefficientBudget c d b i.val j.val ≤ 4*(r:ℝ)^2*C*D := by
  have hterm1 (k : ℕ) (hk : k ∈ Finset.range (j.val+1)) :
      ‖d (j.val-k)‖*‖responseCoefficient c b (i.val+k+1)‖ ≤ (2*(r:ℝ))*C*D := by
    have hkn : k ≤ j.val := by simpa using hk
    have hd1 := hd (j.val-k) (by omega)
    have hc1 := responseCoefficient_bound_order c b (2*r) C hC hc (i.val+k+1) (by omega)
    push_cast at hc1
    exact (mul_le_mul hd1 hc1 (norm_nonneg _) hD).trans_eq (by ring)
  have hterm2 (k : ℕ) (hk : k ∈ Finset.range (j.val+1)) :
      ‖responseCoefficient c b (j.val-k)‖*‖d (i.val+k+1)‖ ≤ (2*(r:ℝ))*C*D := by
    have hkn : k ≤ j.val := by simpa using hk
    have hc1 := responseCoefficient_bound_order c b (2*r) C hC hc (j.val-k) (by omega)
    have hd1 := hd (i.val+k+1) (by omega)
    push_cast at hc1
    exact mul_le_mul hc1 hd1 (norm_nonneg _) (by positivity)
  have hsum1 := Finset.sum_le_sum (s:=Finset.range (j.val+1)) hterm1
  have hsum2 := Finset.sum_le_sum (s:=Finset.range (j.val+1)) hterm2
  have hj : ((j.val+1:ℕ):ℝ) ≤ (r:ℝ) := by exact_mod_cast j.isLt
  have hcoef : 0 ≤ (2*(r:ℝ))*C*D := by positivity
  have hsum : (∑ k ∈ Finset.range (j.val+1), ((2*(r:ℝ))*C*D)) ≤ (r:ℝ)*((2*(r:ℝ))*C*D) := by
    simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right hj hcoef
  unfold coefficientBudget
  nlinarith [hsum1,hsum2,hsum]

theorem directionalBudget_bound_order (c d : ℕ → ℂ) (b : Bool) (r : ℕ) (C D : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hc : ∀ k ≤ 2*r, ‖c k‖ ≤ C) (hd : ∀ k ≤ 2*r, ‖d k‖ ≤ D)
    (x y : Fin r → ℝ) :
    directionalBudget c d b r x y ≤ 4*(r:ℝ)^2*C*D * coordMass x * coordMass y := by
  let K : ℝ := 4*(r:ℝ)^2*C*D
  have hpoint (i j : Fin r) :
      |x i| *coefficientBudget c d b i.val j.val* |y j| ≤ |x i| *K* |y j| := by
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    exact mul_le_mul_of_nonneg_left (coefficientBudget_bound_order c d b r C D hC hD hc hd i j) (abs_nonneg _)
  have hsum : (∑ i : Fin r, ∑ j : Fin r, |x i| * coefficientBudget c d b i.val j.val * |y j|) ≤
      (∑ i : Fin r, ∑ j : Fin r, |x i| * K * |y j|) := by
    exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hpoint i j))
  have he : (∑ i : Fin r, ∑ j : Fin r, |x i| *K* |y j|) = K * coordMass x * coordMass y := by
    unfold coordMass
    simp only [Finset.mul_sum,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  change directionalBudget c d b r x y ≤ K * coordMass x * coordMass y
  unfold directionalBudget
  exact hsum.trans_eq he

/-- Explicit polynomial order factor; the four coefficient bounds are for
the same two complete, independently repartitioned source arguments. -/
theorem repartition_explicit_order_bound (M P : ℕ) (U V : ℕ → ℂ) (b : Bool) (r : ℕ)
    (AL BL AR BR : ℝ) (hAL : 0 ≤ AL) (hBL : 0 ≤ BL) (hAR : 0 ≤ AR) (hBR : 0 ≤ BR)
    (hheadL : ∀ k ≤ 2*r, ‖repHead M U k‖ ≤ AL)
    (htailL : ∀ k ≤ 2*r, ‖repTail M U k‖ ≤ BL)
    (hheadR : ∀ k ≤ 2*r, ‖repHead P V k‖ ≤ AR)
    (htailR : ∀ k ≤ 2*r, ‖repTail P V k‖ ≤ BR)
    (x y : Fin r → ℝ) :
    ‖(matrixPair (coefficientBlock (sourceKernel nativeC b) r) x y : ℂ) -
      coefficientPair (repHead M U) (repHead P V) b r x y‖ ≤
      (4*(r:ℝ)^2*(AL*BR + BL*AR + BL*BR))*coordMass x*coordMass y := by
  have h1 := mixed_direction_bound (repHead M U) (repTail P V) b r x y
  have h2 := mixed_direction_bound (repTail M U) (repHead P V) b r x y
  have h3 := mixed_direction_bound (repTail M U) (repTail P V) b r x y
  have he : ‖(matrixPair (coefficientBlock (sourceKernel nativeC b) r) x y : ℂ) -
      coefficientPair (repHead M U) (repHead P V) b r x y‖ ≤ repError M P U V b r x y := by
    rw [repartition_original_four_terms]
    rw [show coefficientPair (repHead M U) (repHead P V) b r x y +
      coefficientPair (repHead M U) (repTail P V) b r x y +
      coefficientPair (repTail M U) (repHead P V) b r x y +
      coefficientPair (repTail M U) (repTail P V) b r x y -
      coefficientPair (repHead M U) (repHead P V) b r x y =
      (coefficientPair (repHead M U) (repTail P V) b r x y +
       coefficientPair (repTail M U) (repHead P V) b r x y) +
       coefficientPair (repTail M U) (repTail P V) b r x y by ring]
    unfold repError
    exact (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add h1 h2)) h3)
  have ha := directionalBudget_bound_order (repHead M U) (repTail P V) b r AL BR hAL hBR hheadL htailR x y
  have hb := directionalBudget_bound_order (repTail M U) (repHead P V) b r BL AR hBL hAR htailL hheadR x y
  have hc := directionalBudget_bound_order (repTail M U) (repTail P V) b r BL BR hBL hBR htailL htailR x y
  refine he.trans ?_
  unfold repError
  calc
    _ ≤ (4*(r:ℝ)^2*AL*BR * coordMass x * coordMass y) +
        (4*(r:ℝ)^2*BL*AR * coordMass x * coordMass y) +
        (4*(r:ℝ)^2*BL*BR * coordMass x * coordMass y) := add_le_add (add_le_add ha hb) hc
    _ = _ := by ring

#print axioms repartition_explicit_order_bound

#print axioms directionalBudget_bound_order

#print axioms coefficientBudget_bound_order
end
end CarryUniformSource
