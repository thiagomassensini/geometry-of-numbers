import CoefficientLaw

namespace CarrySourceBezout
open scoped BigOperators
noncomputable section
set_option autoImplicit false

/-- Replace one coefficient by its old value plus a chosen displacement. -/
def sourceCoefficientUpdate (c : ℕ → ℝ) (m : ℕ) (δ : ℝ) : ℕ → ℝ :=
  fun r => if r = m then c r + δ else c r

theorem sourceCoefficientUpdate_eq_of_lt (c : ℕ → ℝ) (m : ℕ) (δ : ℝ)
    (r : ℕ) (hr : r < m) : sourceCoefficientUpdate c m δ r = c r := by
  simp [sourceCoefficientUpdate, Nat.ne_of_lt hr]

def lastCoordinateMatrix (n : ℕ) (a : ℝ) : Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  fun i j => if i.val = n ∧ j.val = n then a else 0

theorem sourceKernel_even_last_update (c : ℕ → ℝ) (n : ℕ) (δ : ℝ) :
    PowerSeries.coeff n (PowerSeries.coeff n
      (sourceKernel (sourceCoefficientUpdate c (2*n+1) δ) false)) =
        PowerSeries.coeff n (PowerSeries.coeff n (sourceKernel c false)) -
          (2*n+1 : ℝ) * c 0 * δ := by
  rw [sourceKernel_even_coefficient_explicit, sourceKernel_even_coefficient_explicit]
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  have hsum :
      (∑ k ∈ Finset.range n,
        ((n : ℝ) - n - 2*k - 1) *
          sourceCoefficientUpdate c (2*n+1) δ (n-k) *
          sourceCoefficientUpdate c (2*n+1) δ (n+k+1)) =
        ∑ k ∈ Finset.range n,
          ((n : ℝ) - n - 2*k - 1) * c (n-k) * c (n+k+1) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hkn : k < n := by simpa using hk
    have hleft : n-k < 2*n+1 := by omega
    have hright : n+k+1 < 2*n+1 := by omega
    simp only [sourceCoefficientUpdate, if_neg (Nat.ne_of_lt hleft),
      if_neg (Nat.ne_of_lt hright)]
  rw [hsum]
  have hzero : sourceCoefficientUpdate c (2*n+1) δ 0 = c 0 :=
    sourceCoefficientUpdate_eq_of_lt c (2*n+1) δ 0 (by omega)
  have hlast : sourceCoefficientUpdate c (2*n+1) δ (n+n+1) = c (n+n+1) + δ := by
    have hm : n+n+1 = 2*n+1 := by omega
    simp [sourceCoefficientUpdate, hm]
  rw [show n-n = 0 by omega, hzero, hlast]
  ring

theorem sourceKernel_odd_last_update (c : ℕ → ℝ) (n : ℕ) (δ : ℝ) :
    PowerSeries.coeff n (PowerSeries.coeff n
      (sourceKernel (sourceCoefficientUpdate c (2*n+2) δ) true)) =
        PowerSeries.coeff n (PowerSeries.coeff n (sourceKernel c true)) -
          (2*n+2 : ℝ) * c 0 * δ := by
  rw [sourceKernel_odd_coefficient_explicit, sourceKernel_odd_coefficient_explicit]
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  have hsum :
      (∑ k ∈ Finset.range n,
        (((n-k+1 : ℕ) : ℝ) *
            sourceCoefficientUpdate c (2*n+2) δ (n-k+1) *
            sourceCoefficientUpdate c (2*n+2) δ (n+k+1) -
          ((n+k+2 : ℕ) : ℝ) *
            sourceCoefficientUpdate c (2*n+2) δ (n-k) *
            sourceCoefficientUpdate c (2*n+2) δ (n+k+2))) =
        ∑ k ∈ Finset.range n,
          (((n-k+1 : ℕ) : ℝ) * c (n-k+1) * c (n+k+1) -
            ((n+k+2 : ℕ) : ℝ) * c (n-k) * c (n+k+2)) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hkn : k < n := by simpa using hk
    have h1 : n-k+1 < 2*n+2 := by omega
    have h2 : n+k+1 < 2*n+2 := by omega
    have h3 : n-k < 2*n+2 := by omega
    have h4 : n+k+2 < 2*n+2 := by omega
    simp only [sourceCoefficientUpdate, if_neg (Nat.ne_of_lt h1),
      if_neg (Nat.ne_of_lt h2), if_neg (Nat.ne_of_lt h3),
      if_neg (Nat.ne_of_lt h4)]
  rw [hsum]
  have hone : sourceCoefficientUpdate c (2*n+2) δ (n-n+1) = c (n-n+1) :=
    sourceCoefficientUpdate_eq_of_lt c (2*n+2) δ (n-n+1) (by omega)
  have hone' : sourceCoefficientUpdate c (2*n+2) δ (n+n+1) = c (n+n+1) :=
    sourceCoefficientUpdate_eq_of_lt c (2*n+2) δ (n+n+1) (by omega)
  have hzero : sourceCoefficientUpdate c (2*n+2) δ (n-n) = c 0 := by
    rw [show n-n = 0 by omega]
    exact sourceCoefficientUpdate_eq_of_lt c (2*n+2) δ 0 (by omega)
  have hlast : sourceCoefficientUpdate c (2*n+2) δ (n+n+2) = c (n+n+2) + δ := by
    have hm : n+n+2 = 2*n+2 := by omega
    simp [sourceCoefficientUpdate, hm]
  rw [hone, hone', hzero, hlast]
  simp only [Nat.sub_self]
  push_cast
  ring

/-- The only coefficient at order `2*n+s+1` entering the `(n+1)`-block is
the last diagonal entry. This is a rank-one symmetric update. -/
theorem sourceBezout_lastCoefficient_rankOne
    (c : ℕ → ℝ) (n : ℕ) (b : Bool) (δ : ℝ) :
    coefficientBlock
        (sourceKernel (sourceCoefficientUpdate c (if b then 2*n+2 else 2*n+1) δ) b) (n+1) =
      coefficientBlock (sourceKernel c b) (n+1) +
        lastCoordinateMatrix n
          (-((if b then 2*n+2 else 2*n+1 : ℕ) : ℝ) * c 0 * δ) := by
  cases b with
  | false =>
      simp only [Bool.false_eq_true, if_false]
      ext i j
      by_cases hi : i.val = n
      · by_cases hj : j.val = n
        · have hi' : i = Fin.last n := Fin.ext hi
          have hj' : j = Fin.last n := Fin.ext hj
          subst i
          subst j
          simp [Matrix.add_apply, coefficientBlock, lastCoordinateMatrix]
          rw [sourceKernel_even_last_update]
          ring
        · have hcut : i.val+j.val+1 < 2*n+1 := by omega
          have hp : ∀ r, r ≤ i.val+j.val+1 →
              sourceCoefficientUpdate c (2*n+1) δ r = c r := by
            intro r hr
            exact sourceCoefficientUpdate_eq_of_lt c (2*n+1) δ r (by omega)
          have he := sourceKernel_coefficient_depends_on_prefix
            (sourceCoefficientUpdate c (2*n+1) δ) c false i.val j.val hp
          simpa [coefficientBlock, lastCoordinateMatrix, hi, hj] using he
      · have hcut : i.val+j.val+1 < 2*n+1 := by omega
        have hp : ∀ r, r ≤ i.val+j.val+1 →
            sourceCoefficientUpdate c (2*n+1) δ r = c r := by
          intro r hr
          exact sourceCoefficientUpdate_eq_of_lt c (2*n+1) δ r (by omega)
        have he := sourceKernel_coefficient_depends_on_prefix
          (sourceCoefficientUpdate c (2*n+1) δ) c false i.val j.val hp
        simpa [coefficientBlock, lastCoordinateMatrix, hi] using he
  | true =>
      simp only [if_true]
      ext i j
      by_cases hi : i.val = n
      · by_cases hj : j.val = n
        · have hi' : i = Fin.last n := Fin.ext hi
          have hj' : j = Fin.last n := Fin.ext hj
          subst i
          subst j
          simp [Matrix.add_apply, coefficientBlock, lastCoordinateMatrix]
          rw [sourceKernel_odd_last_update]
          ring
        · have hcut : i.val+j.val+2 < 2*n+2 := by omega
          have hp : ∀ r, r ≤ i.val+j.val+2 →
              sourceCoefficientUpdate c (2*n+2) δ r = c r := by
            intro r hr
            exact sourceCoefficientUpdate_eq_of_lt c (2*n+2) δ r (by omega)
          have he := sourceKernel_coefficient_depends_on_prefix
            (sourceCoefficientUpdate c (2*n+2) δ) c true i.val j.val hp
          simpa [coefficientBlock, lastCoordinateMatrix, hi, hj] using he
      · have hcut : i.val+j.val+2 < 2*n+2 := by omega
        have hp : ∀ r, r ≤ i.val+j.val+2 →
            sourceCoefficientUpdate c (2*n+2) δ r = c r := by
          intro r hr
          exact sourceCoefficientUpdate_eq_of_lt c (2*n+2) δ r (by omega)
        have he := sourceKernel_coefficient_depends_on_prefix
          (sourceCoefficientUpdate c (2*n+2) δ) c true i.val j.val hp
        simpa [coefficientBlock, lastCoordinateMatrix, hi] using he

#print axioms sourceKernel_even_last_update
#print axioms sourceKernel_odd_last_update
#print axioms sourceBezout_lastCoefficient_rankOne

end
end CarrySourceBezout
