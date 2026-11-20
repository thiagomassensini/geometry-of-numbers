import GroupedSourceBudget
import KernelBudget

/-! Support control: the correlated TFVD source perturbation reads only
a finite prefix of the SAME original even completed C3 coefficient jet.
This is separate from interval evaluation of the jet values. -/
namespace CarrySourceBezout
noncomputable section
set_option maxHeartbeats 1200000

theorem response_odd_explicit (c : ℕ → ℂ) (k : ℕ) :
    responseCoefficient c true k = -((k+1:ℕ):ℂ)*c (k+1) := by
  simp [responseCoefficient, sourceResponse, PowerSeries.coeff_derivative,
    sourceSeries]
  ring

theorem response_even_zero (c : ℕ → ℂ) :
    responseCoefficient c false 0 = 0 := by
  simp [responseCoefficient, sourceResponse]

theorem response_even_succ (c : ℕ → ℂ) (k : ℕ) :
    responseCoefficient c false (k+1) =
      -((k+1:ℕ):ℂ)*c (k+1) := by
  simp [responseCoefficient, sourceResponse, PowerSeries.coeff_succ_X_mul,
    PowerSeries.coeff_derivative, sourceSeries]
  ring


/-- A response coefficient reads no jet later than k+1. -/
theorem response_agree_below (c d : ℕ → ℂ) (b : Bool)
    (k N : ℕ) (hk : k+1 < N)
    (hAgree : ∀ t, t < N → c t = d t) :
    responseCoefficient c b k = responseCoefficient d b k := by
  cases b with
  | true =>
    rw [response_odd_explicit, response_odd_explicit, hAgree _ hk]
  | false =>
    cases k with
    | zero =>
      rw [response_even_zero, response_even_zero]
    | succ k =>
      rw [response_even_succ, response_even_succ]
      congr 1
      exact hAgree (k+1) (by omega)

/-- A mixed source kernel coefficient at (i,j) depends only on jets
strictly below index i+j+3. This includes response AND companion legs. -/
theorem mixed_kernel_agree_below
    (c c' d d' : ℕ → ℂ) (b : Bool) (i j N : ℕ)
    (hN : i+j+2 < N)
    (hc : ∀ t, t < N → c t = c' t)
    (hd : ∀ t, t < N → d t = d' t) :
    PowerSeries.coeff j (PowerSeries.coeff i (mixedSourceKernel c d b)) =
      PowerSeries.coeff j (PowerSeries.coeff i (mixedSourceKernel c' d' b)) := by
  rw [mixed_kernel_coefficient, mixed_kernel_coefficient]
  congr 1
  · apply Finset.sum_congr rfl
    intro k hk
    have hkj : k ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    rw [hd (j-k) (by omega),
      response_agree_below c c' b (i+k+1) N (by omega) hc]
  · apply Finset.sum_congr rfl
    intro k hk
    have hkj : k ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    rw [response_agree_below c c' b (j-k) N (by omega) hc,
      hd (i+k+1) (by omega)]

/-- Exact matrix-level locality: r by r source blocks only consume the
first 2r+1 completed coefficient jets of each source argument. -/
theorem coefficientPair_agree_below
    (c c' d d' : ℕ → ℂ) (b : Bool) (r N : ℕ)
    (x y : Fin r → ℝ)
    (hN : 2*r < N)
    (hc : ∀ t, t < N → c t = c' t)
    (hd : ∀ t, t < N → d t = d' t) :
    coefficientPair c d b r x y = coefficientPair c' d' b r x y := by
  have he : coefficientBlock (mixedSourceKernel c d b) r =
      coefficientBlock (mixedSourceKernel c' d' b) r := by
    ext i j
    apply mixed_kernel_agree_below c c' d d' b i.val j.val N
      (by have hi := i.isLt; have hj := j.isLt; omega) hc hd
  unfold coefficientPair
  rw [he]

def prefixTail (N : ℕ) (T : ℕ → ℂ) : ℕ → ℂ :=
  fun t => if t < N then T t else 0

theorem signed_linear_prefixTail
    (alpha betaA : ℝ) (bB bP : Bool) (rB rP N : ℕ)
    (zB : Fin rB → ℝ) (zP : Fin rP → ℝ)
    (H T : ℕ → ℂ) (hNB : 2*rB < N) (hNP : 2*rP < N) :
    signedSourceLinear alpha betaA bB bP rB rP zB zP H T =
      signedSourceLinear alpha betaA bB bP rB rP zB zP H (prefixTail N T) := by
  have htail : ∀ t, t < N → T t = prefixTail N T t := by
    intro t ht
    simp [prefixTail,ht]
  unfold signedSourceLinear signedSourcePair
  rw [coefficientPair_agree_below H H T (prefixTail N T) bB rB N zB zB
        hNB (by intros; rfl) htail,
      coefficientPair_agree_below H H T (prefixTail N T) bP rP N zP zP
        hNP (by intros; rfl) htail,
      coefficientPair_agree_below T (prefixTail N T) H H bB rB N zB zB
        hNB htail (by intros; rfl),
      coefficientPair_agree_below T (prefixTail N T) H H bP rP N zP zP
        hNP htail (by intros; rfl)]

end
end CarrySourceBezout
