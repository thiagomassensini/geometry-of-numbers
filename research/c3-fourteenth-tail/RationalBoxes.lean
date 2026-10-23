import InfiniteC3Tail
import Mathlib.Analysis.Real.Pi.Bounds

namespace CarryC3Boxes
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1500000

/-- Rational enclosures for evaluation, never a modification of the source. -/
structure Box where
  lo : ℚ
  hi : ℚ
  deriving DecidableEq, Repr

def Box.Contains (a : Box) (x : ℝ) : Prop := (a.lo:ℝ) ≤ x ∧ x ≤ a.hi
def Box.Subset (a b : Box) : Prop := b.lo ≤ a.lo ∧ a.hi ≤ b.hi
instance (a b : Box) : Decidable (a.Subset b) := inferInstanceAs (Decidable (_ ∧ _))
def Box.point (q : ℚ) : Box := ⟨q,q⟩
def Box.add (a b : Box) : Box := ⟨a.lo+b.lo,a.hi+b.hi⟩
def Box.neg (a : Box) : Box := ⟨-a.hi,-a.lo⟩
def Box.sub (a b : Box) : Box := a.add b.neg
def Box.mul (a b : Box) : Box :=
  ⟨min (min (a.lo*b.lo) (a.lo*b.hi)) (min (a.hi*b.lo) (a.hi*b.hi)),
   max (max (a.lo*b.lo) (a.lo*b.hi)) (max (a.hi*b.lo) (a.hi*b.hi))⟩
def Box.inv (a : Box) : Box := ⟨a.hi⁻¹,a.lo⁻¹⟩
def Box.expand (a : Box) (e : ℚ) : Box := ⟨a.lo-e,a.hi+e⟩

theorem Box.point_contains (q : ℚ) : (Box.point q).Contains q := ⟨le_rfl,le_rfl⟩

theorem Box.subset_contains {a b : Box} {x : ℝ} (h : a.Subset b) (hx : a.Contains x) :
    b.Contains x := by
  have hl : (b.lo:ℝ) ≤ a.lo := by exact_mod_cast h.1
  have hu : (a.hi:ℝ) ≤ b.hi := by exact_mod_cast h.2
  exact ⟨hl.trans hx.1,hx.2.trans hu⟩

theorem Box.add_contains {a b : Box} {x y : ℝ} (hx : a.Contains x) (hy : b.Contains y) :
    (a.add b).Contains (x+y) := by
  constructor
  · simpa only [Box.add,Rat.cast_add] using add_le_add hx.1 hy.1
  · simpa only [Box.add,Rat.cast_add] using add_le_add hx.2 hy.2

theorem Box.neg_contains {a : Box} {x : ℝ} (hx : a.Contains x) : a.neg.Contains (-x) := by
  constructor
  · simpa only [Box.neg,Rat.cast_neg] using neg_le_neg hx.2
  · simpa only [Box.neg,Rat.cast_neg] using neg_le_neg hx.1

theorem Box.sub_contains {a b : Box} {x y : ℝ} (hx : a.Contains x) (hy : b.Contains y) :
    (a.sub b).Contains (x-y) := by simpa only [Box.sub,sub_eq_add_neg] using Box.add_contains hx (Box.neg_contains hy)

theorem endpoint_mul_bounds (l u v w x y : ℝ) (hl : l ≤ x) (hu : x ≤ u) (hv : v ≤ y) (hw : y ≤ w) :
    min (min (l*v) (l*w)) (min (u*v) (u*w)) ≤ x*y ∧
      x*y ≤ max (max (l*v) (l*w)) (max (u*v) (u*w)) := by
  have ho : min (l*v) (l*w) ≤ l*y ∧ l*y ≤ max (l*v) (l*w) := by
    by_cases hh : 0 ≤ l
    · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_left hv hh),
        (mul_le_mul_of_nonneg_left hw hh).trans (le_max_right _ _)⟩
    · have hh := le_of_lt (lt_of_not_ge hh)
      exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_left hw hh),
        (mul_le_mul_of_nonpos_left hv hh).trans (le_max_left _ _)⟩
  have hp : min (u*v) (u*w) ≤ u*y ∧ u*y ≤ max (u*v) (u*w) := by
    by_cases hh : 0 ≤ u
    · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_left hv hh),
        (mul_le_mul_of_nonneg_left hw hh).trans (le_max_right _ _)⟩
    · have hh := le_of_lt (lt_of_not_ge hh)
      exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_left hw hh),
        (mul_le_mul_of_nonpos_left hv hh).trans (le_max_left _ _)⟩
  by_cases hy : 0 ≤ y
  · exact ⟨(min_le_left _ _).trans (ho.1.trans (mul_le_mul_of_nonneg_right hl hy)),
      ((mul_le_mul_of_nonneg_right hu hy).trans hp.2).trans (le_max_right _ _)⟩
  · have hy := le_of_lt (lt_of_not_ge hy)
    exact ⟨(min_le_right _ _).trans (hp.1.trans (mul_le_mul_of_nonpos_right hu hy)),
      ((mul_le_mul_of_nonpos_right hl hy).trans ho.2).trans (le_max_left _ _)⟩

theorem Box.mul_contains {a b : Box} {x y : ℝ} (hx : a.Contains x) (hy : b.Contains y) :
    (a.mul b).Contains (x*y) := by
  simpa only [Box.mul,Box.Contains,Rat.cast_min,Rat.cast_max,Rat.cast_mul] using
    endpoint_mul_bounds a.lo a.hi b.lo b.hi x y hx.1 hx.2 hy.1 hy.2

theorem Box.inv_contains {a : Box} {x : ℝ} (hx : a.Contains x)
    (h : 0 < a.lo ∨ a.hi < 0) : a.inv.Contains x⁻¹ := by
  rcases h with h | h
  · have hl : (0:ℝ)<a.lo := by exact_mod_cast h
    constructor
    · simpa only [Box.inv,Rat.cast_inv] using inv_anti₀ (hl.trans_le hx.1) hx.2
    · simpa only [Box.inv,Rat.cast_inv] using inv_anti₀ hl hx.1
  · have hu : (a.hi:ℝ)<0 := by exact_mod_cast h
    have hn : 0 < -x := by linarith [hx.2]
    have hn2 : 0 < -(a.hi:ℝ) := by linarith
    constructor
    · have hh := inv_anti₀ hn2 (neg_le_neg hx.2)
      simpa only [inv_neg,neg_le_neg_iff,Box.inv,Rat.cast_inv] using hh
    · have hh := inv_anti₀ hn (neg_le_neg hx.1)
      simpa only [inv_neg,neg_le_neg_iff,Box.inv,Rat.cast_inv] using hh

def gridScale : ℚ := 10^30
def roundLower (x : ℚ) : ℚ := (⌊x*gridScale⌋:ℚ)/gridScale
def roundUpper (x : ℚ) : ℚ := ((⌊x*gridScale⌋+1:ℤ):ℚ)/gridScale
def Box.round (a : Box) : Box := ⟨roundLower a.lo,roundUpper a.hi⟩

theorem round_lower_le (x : ℚ) : roundLower x ≤ x := by
  unfold roundLower
  apply (div_le_iff₀ (by norm_num [gridScale] : (0:ℚ)<gridScale)).2
  exact Int.floor_le _

theorem le_round_upper (x : ℚ) : x ≤ roundUpper x := by
  unfold roundUpper
  apply (le_div_iff₀ (by norm_num [gridScale] : (0:ℚ)<gridScale)).2
  simpa only [Int.cast_add,Int.cast_one] using le_of_lt (Int.lt_floor_add_one (x*gridScale))

theorem Box.round_contains {a : Box} {x : ℝ} (hx : a.Contains x) : a.round.Contains x := by
  constructor
  · exact le_trans (by exact_mod_cast round_lower_le a.lo) hx.1
  · exact le_trans hx.2 (by exact_mod_cast le_round_upper a.hi)

def badd (a b : Box) : Box := (a.add b).round
def bmul (a b : Box) : Box := (a.mul b).round
def bneg (a : Box) : Box := a.neg
def bsub (a b : Box) : Box := (a.sub b).round
def binv (a : Box) : Box := a.inv.round
def bpow (a : Box) : ℕ → Box
  | 0 => Box.point 1
  | n+1 => bmul (bpow a n) a
def bsum (a : ℕ → Box) : ℕ → Box
  | 0 => Box.point 0
  | n+1 => badd (bsum a n) (a n)

theorem badd_contains {a b : Box} {x y : ℝ} (hx : a.Contains x) (hy : b.Contains y) :
    (badd a b).Contains (x+y) := Box.round_contains (Box.add_contains hx hy)
theorem bmul_contains {a b : Box} {x y : ℝ} (hx : a.Contains x) (hy : b.Contains y) :
    (bmul a b).Contains (x*y) := Box.round_contains (Box.mul_contains hx hy)
theorem bsub_contains {a b : Box} {x y : ℝ} (hx : a.Contains x) (hy : b.Contains y) :
    (bsub a b).Contains (x-y) := Box.round_contains (Box.sub_contains hx hy)
theorem binv_contains {a : Box} {x : ℝ} (hx : a.Contains x) (h : 0<a.lo ∨ a.hi<0) :
    (binv a).Contains x⁻¹ := Box.round_contains (Box.inv_contains hx h)
theorem bpow_contains {a : Box} {x : ℝ} (hx : a.Contains x) (n : ℕ) :
    (bpow a n).Contains (x^n) := by
  induction n with
  | zero => simpa only [bpow,pow_zero,Rat.cast_one] using Box.point_contains 1
  | succ n ih => simpa only [bpow,pow_succ] using bmul_contains ih hx
theorem bsum_contains (N : ℕ) (a : ℕ → Box) (f : ℕ → ℝ)
    (h : ∀ j<N, (a j).Contains (f j)) :
    (bsum a N).Contains (∑ j ∈ Finset.range N, f j) := by
  induction N with
  | zero => simpa only [bsum,Finset.range_zero,Finset.sum_empty,Rat.cast_zero] using Box.point_contains 0
  | succ N ih =>
    rw [Finset.sum_range_succ]
    exact badd_contains (ih (fun j hj => h j (by omega))) (h N (by omega))

theorem Box.expand_contains {a : Box} {e : ℚ} {x y : ℝ}
    (hx : a.Contains x) (herr : |y-x| ≤ (e:ℝ)) : (a.expand e).Contains y := by
  have he := abs_le.mp herr
  constructor <;> dsimp only [Box.expand]
  · rw [Rat.cast_sub]; linarith [hx.1]
  · rw [Rat.cast_add]; linarith [hx.2]

end CarryC3Boxes
