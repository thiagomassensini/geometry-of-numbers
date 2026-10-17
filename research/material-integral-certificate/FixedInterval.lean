import IntervalHelpers

/-! Computable outward-rounded integer intervals. `all` represents a failed
numerical enclosure, never a mathematical assumption. -/
namespace CarryIntegralCertificate
open CarryMaterialPivotCertificate
set_option autoImplicit false

def intervalScale : ℤ := 10^60

private theorem scale_pos : (0:ℝ) < (intervalScale:ℝ) := by norm_num [intervalScale]
private theorem scale_pos_int : (0:ℤ) < intervalScale := by norm_num [intervalScale]

inductive Box where
  | all
  | finite (lo hi : ℤ)
  deriving DecidableEq, Repr

def Box.Mem (i : Box) (x : ℝ) : Prop := match i with
  | .all => True
  | .finite l u => (l:ℝ) ≤ (intervalScale:ℝ)*x ∧ (intervalScale:ℝ)*x ≤ (u:ℝ)

def Box.point (n : ℤ) : Box := .finite (n*intervalScale) (n*intervalScale)
def Box.add : Box → Box → Box
  | .finite a b,.finite c d => .finite (a+c) (b+d)
  | _,_ => .all

def Box.neg : Box → Box
  | .finite a b => .finite (-b) (-a)
  | _ => .all

def intFloor (a d : ℤ) : ℤ := a/d
def intCeil (a d : ℤ) : ℤ := -((-a)/d)

def Box.mul : Box → Box → Box
  | .finite a b,.finite c d =>
    .finite (intFloor (if 0 ≤ a ∧ 0 ≤ c then a*c else min (min (a*c) (a*d)) (min (b*c) (b*d))) intervalScale)
      (intCeil (if 0 ≤ a ∧ 0 ≤ c then b*d else max (max (a*c) (a*d)) (max (b*c) (b*d))) intervalScale)
  | _,_ => .all

def Box.inv : Box → Box
  | .finite a b => if 0 < a then
      .finite (intFloor (intervalScale*intervalScale) b)
        (intCeil (intervalScale*intervalScale) a) else .all
  | _ => .all

def Box.div (i j : Box) : Box := i.mul j.inv

/-- A positive interval power is evaluated directly on its integer endpoints.
This avoids duplicating a nested interval product during kernel reduction. -/
def Box.pow : Box → ℕ → Box
  | _,0 => .point 1
  | .all,_+1 => .all
  | .finite a b,n+1 => if 0 ≤ a then
      .finite (intFloor (a^(n+1)) (intervalScale^n))
        (intCeil (b^(n+1)) (intervalScale^n))
    else ((Box.finite a b).pow n).mul (.finite a b)

theorem mem_point (n : ℤ) : (Box.point n).Mem (n:ℝ) := by
  simp [Box.point,Box.Mem,mul_comm]

theorem mem_add {i j : Box} {x y : ℝ} (hx : i.Mem x) (hy : j.Mem y) :
    (i.add j).Mem (x+y) := by
  cases i with
  | all => trivial
  | finite a b =>
    cases j with
    | all => trivial
    | finite c d =>
      simp only [Box.Mem,Box.add,Int.cast_add] at *
      constructor <;> nlinarith only [hx.1,hx.2,hy.1,hy.2]

theorem mem_neg {i : Box} {x : ℝ} (hx : i.Mem x) : i.neg.Mem (-x) := by
  cases i with
  | all => trivial
  | finite a b =>
    simp only [Box.Mem,Box.neg,Int.cast_neg] at *
    constructor <;> nlinarith only [hx.1,hx.2]

private theorem floor_mul_le (a : ℤ) {d : ℤ} (hd : 0 < d) :
    intFloor a d*d ≤ a := Int.ediv_mul_le a (ne_of_gt hd)

private theorem le_ceil_mul (a : ℤ) {d : ℤ} (hd : 0 < d) :
    a ≤ intCeil a d*d := by
  have h := floor_mul_le (-a) hd
  dsimp [intCeil,intFloor] at *
  nlinarith

theorem mem_mul {i j : Box} {x y : ℝ} (hx : i.Mem x) (hy : j.Mem y) :
    (i.mul j).Mem (x*y) := by
  cases i with
  | all => trivial
  | finite a b =>
    cases j with
    | all => trivial
    | finite c d =>
      let l := if 0 ≤ a ∧ 0 ≤ c then a*c else min (min (a*c) (a*d)) (min (b*c) (b*d))
      let u := if 0 ≤ a ∧ 0 ≤ c then b*d else max (max (a*c) (a*d)) (max (b*c) (b*d))
      have hm : (l:ℝ) ≤ ((intervalScale:ℝ)*x)*((intervalScale:ℝ)*y) ∧
          ((intervalScale:ℝ)*x)*((intervalScale:ℝ)*y) ≤ (u:ℝ) := by
        by_cases hac : 0 ≤ a ∧ 0 ≤ c
        · have haR : (0:ℝ) ≤ (a:ℝ) := by exact_mod_cast hac.1
          have hcR : (0:ℝ) ≤ (c:ℝ) := by exact_mod_cast hac.2
          simp only [l,u,if_pos hac,Int.cast_mul]
          exact ⟨mul_le_mul hx.1 hy.1 hcR (haR.trans hx.1),
            mul_le_mul hx.2 hy.2 (hcR.trans hy.1) (haR.trans (hx.1.trans hx.2))⟩
        · simp only [l,u,if_neg hac]
          apply enclose_mul hx hy
          all_goals exact_mod_cast (by omega : _)
      have hl : (intFloor l intervalScale:ℝ)*(intervalScale:ℝ) ≤ (l:ℝ) := by
        exact_mod_cast floor_mul_le l scale_pos_int
      have hu : (u:ℝ) ≤ (intCeil u intervalScale:ℝ)*(intervalScale:ℝ) := by
        exact_mod_cast le_ceil_mul u scale_pos_int
      change (intFloor l intervalScale:ℝ) ≤ (intervalScale:ℝ)*(x*y) ∧
        (intervalScale:ℝ)*(x*y) ≤ (intCeil u intervalScale:ℝ)
      constructor
      · apply (mul_le_mul_iff_right₀ scale_pos).mp
        calc
          _ ≤ (l:ℝ) := by nlinarith only [hl]
          _ ≤ _ := hm.1
          _ = _ := by ring
      · apply (mul_le_mul_iff_right₀ scale_pos).mp
        calc
          _ = ((intervalScale:ℝ)*x)*((intervalScale:ℝ)*y) := by ring
          _ ≤ (u:ℝ) := hm.2
          _ ≤ _ := by nlinarith only [hu]

theorem mem_inv {i : Box} {x : ℝ} (hx : i.Mem x) : i.inv.Mem (1/x) := by
  cases i with
  | all => trivial
  | finite a b =>
    by_cases ha : 0 < a
    · have haR : (0:ℝ) < (a:ℝ) := by exact_mod_cast ha
      have hbR : (0:ℝ) < (b:ℝ) := haR.trans_le (hx.1.trans hx.2)
      have hb : (0:ℤ) < b := by exact_mod_cast hbR
      have hx0 : (0:ℝ) < x := by nlinarith only [hx.1,haR,scale_pos]
      have hl0 : (0:ℤ) ≤ intFloor (intervalScale*intervalScale) b :=
        Int.ediv_nonneg (mul_self_nonneg _) hb.le
      have hl : (intFloor (intervalScale*intervalScale) b:ℝ)*(b:ℝ) ≤
          (intervalScale:ℝ)*(intervalScale:ℝ) := by
        exact_mod_cast floor_mul_le (intervalScale*intervalScale) hb
      have hu : (intervalScale:ℝ)*(intervalScale:ℝ) ≤
          (intCeil (intervalScale*intervalScale) a:ℝ)*(a:ℝ) := by
        exact_mod_cast le_ceil_mul (intervalScale*intervalScale) ha
      have hu0 : (0:ℝ) ≤ (intCeil (intervalScale*intervalScale) a:ℝ) := by
        have hs := mul_self_nonneg (intervalScale:ℝ)
        nlinarith only [haR,hu,hs]
      simp only [Box.inv,if_pos ha,Box.Mem]
      constructor
      · rw [mul_one_div]
        apply (le_div_iff₀ hx0).mpr
        have h1 := mul_le_mul_of_nonneg_left hx.2 (show (0:ℝ) ≤ (intFloor (intervalScale*intervalScale) b:ℝ) by exact_mod_cast hl0)
        have h2 : (intFloor (intervalScale*intervalScale) b:ℝ)*x ≤ (intervalScale:ℝ) := by
          nlinarith only [h1,hl,scale_pos]
        simpa only [mul_one_div] using h2
      · rw [mul_one_div]
        apply (div_le_iff₀ hx0).mpr
        have h1 := mul_le_mul_of_nonneg_left hx.1 hu0
        have h2 : (intervalScale:ℝ) ≤ (intCeil (intervalScale*intervalScale) a:ℝ)*x := by
          nlinarith only [h1,hu,scale_pos]
        simpa only [mul_one_div] using h2
    · simp [Box.inv,ha,Box.Mem]

theorem mem_div {i j : Box} {x y : ℝ} (hx : i.Mem x) (hy : j.Mem y) :
    (i.div j).Mem (x/y) := by
  have h := mem_mul hx (mem_inv hy)
  simpa only [Box.div,div_eq_mul_inv,one_mul] using h

theorem mem_pow {i : Box} {x : ℝ} (hx : i.Mem x) (n : ℕ) :
    (i.pow n).Mem (x^n) := by
  induction n with
  | zero => simpa only [Box.pow,pow_zero,Int.cast_one] using mem_point 1
  | succ n hn =>
    cases i with
    | all => trivial
    | finite a b =>
      by_cases ha : 0 ≤ a
      · have haR : (0:ℝ) ≤ (a:ℝ) := by exact_mod_cast ha
        have hSn : (0:ℝ) < (intervalScale:ℝ)^n := pow_pos scale_pos n
        have hSnI : (0:ℤ) < intervalScale^n := pow_pos scale_pos_int n
        have hx0 : (0:ℝ) ≤ x := by nlinarith only [haR,hx.1,scale_pos]
        have hxl := pow_le_pow_left₀ haR hx.1 (n+1)
        have hxu := pow_le_pow_left₀ (mul_nonneg scale_pos.le hx0) hx.2 (n+1)
        have hl : (intFloor (a^(n+1)) (intervalScale^n):ℝ)*(intervalScale:ℝ)^n ≤ (a:ℝ)^(n+1) := by
          exact_mod_cast floor_mul_le (a^(n+1)) hSnI
        have hu : (b:ℝ)^(n+1) ≤ (intCeil (b^(n+1)) (intervalScale^n):ℝ)*(intervalScale:ℝ)^n := by
          exact_mod_cast le_ceil_mul (b^(n+1)) hSnI
        simp only [Box.pow,if_pos ha,Box.Mem]
        constructor
        · apply (mul_le_mul_iff_right₀ hSn).mp
          calc
            (intervalScale:ℝ)^n*(intFloor (a^(n+1)) (intervalScale^n):ℝ) =
                (intFloor (a^(n+1)) (intervalScale^n):ℝ)*(intervalScale:ℝ)^n := by ring
            _ ≤ (a:ℝ)^(n+1) := hl
            _ ≤ ((intervalScale:ℝ)*x)^(n+1) := hxl
            _ = _ := by simp only [mul_pow,pow_succ]; ring
        · apply (mul_le_mul_iff_right₀ hSn).mp
          calc
            (intervalScale:ℝ)^n*((intervalScale:ℝ)*x^(n+1)) =
                ((intervalScale:ℝ)*x)^(n+1) := by simp only [mul_pow,pow_succ]; ring
            _ ≤ (b:ℝ)^(n+1) := hxu
            _ ≤ (intCeil (b^(n+1)) (intervalScale^n):ℝ)*(intervalScale:ℝ)^n := hu
            _ = _ := by ring
      · simpa only [Box.pow,if_neg ha,pow_succ] using mem_mul hn hx

/-- Direct rational rounding avoids rounding a tiny reciprocal before
multiplication by its numerator. -/
def Box.rat (a b : ℤ) : Box := if 0 < b then
  .finite (intFloor (a*intervalScale) b) (intCeil (a*intervalScale) b)
  else (Box.point a).div (Box.point b)

theorem mem_rat (a b : ℤ) : (Box.rat a b).Mem ((a:ℝ)/(b:ℝ)) := by
  by_cases hb : 0 < b
  · have hbR : (0:ℝ) < (b:ℝ) := by exact_mod_cast hb
    have hl : (intFloor (a*intervalScale) b:ℝ)*(b:ℝ) ≤ (a:ℝ)*(intervalScale:ℝ) := by
      exact_mod_cast floor_mul_le (a*intervalScale) hb
    have hu : (a:ℝ)*(intervalScale:ℝ) ≤ (intCeil (a*intervalScale) b:ℝ)*(b:ℝ) := by
      exact_mod_cast le_ceil_mul (a*intervalScale) hb
    simp only [Box.rat,if_pos hb,Box.Mem]
    constructor
    · rw [← mul_div_assoc]
      apply (le_div_iff₀ hbR).mpr
      nlinarith only [hl]
    · rw [← mul_div_assoc]
      apply (div_le_iff₀ hbR).mpr
      nlinarith only [hu]
  · simpa only [Box.rat,if_neg hb] using mem_div (mem_point a) (mem_point b)

/-- Join the outward lower endpoint of one enclosure to the upper endpoint
of another. A failed calculation propagates `all`. -/
def Box.outer : Box → Box → Box
  | .finite a _, .finite _ d => .finite a d
  | _,_ => .all

theorem mem_outer {i j : Box} {l x u : ℝ} (hl : i.Mem l) (hu : j.Mem u)
    (hxl : l ≤ x) (hxu : x ≤ u) : (i.outer j).Mem x := by
  cases i with
  | all => trivial
  | finite a b =>
    cases j with
    | all => trivial
    | finite c d =>
      exact ⟨hl.1.trans (mul_le_mul_of_nonneg_left hxl scale_pos.le),
        (mul_le_mul_of_nonneg_left hxu scale_pos.le).trans hu.2⟩

def Box.sum (f : ℕ → Box) : ℕ → Box
  | 0 => .point 0
  | n+1 => (Box.sum f n).add (f n)

theorem mem_sum (f : ℕ → Box) (g : ℕ → ℝ) (n : ℕ)
    (h : ∀ k < n, (f k).Mem (g k)) :
    (Box.sum f n).Mem (∑ k ∈ Finset.range n, g k) := by
  induction n with
  | zero => simpa only [Box.sum,Finset.sum_range_zero,Int.cast_zero] using mem_point 0
  | succ n hn =>
    rw [Box.sum,Finset.sum_range_succ]
    exact mem_add (hn (fun k hk => h k (by omega))) (h n (by omega))

def Box.squares (i : Box) (n : ℕ) : Box := i.pow (2^n)

theorem mem_squares {i : Box} {x : ℝ} (hx : i.Mem x) (n : ℕ) :
    (i.squares n).Mem (x^(2^n)) := mem_pow hx (2^n)

theorem mem_scaled (a : ℤ) : (Box.finite a a).Mem ((a:ℝ)/(intervalScale:ℝ)) := by
  have he : (intervalScale:ℝ)*((a:ℝ)/(intervalScale:ℝ)) = (a:ℝ) := by
    field_simp [ne_of_gt scale_pos]
  change (a:ℝ) ≤ _ ∧ _ ≤ (a:ℝ)
  rw [he]
  exact ⟨le_rfl,le_rfl⟩

def Box.contained : Box → Box → Bool
  | _, .all => true
  | .all, _ => false
  | .finite a b, .finite c d => decide (c ≤ a ∧ b ≤ d)

theorem mem_of_contained {i j : Box} {x : ℝ} (hx : i.Mem x)
    (h : i.contained j = true) : j.Mem x := by
  cases j with
  | all => trivial
  | finite c d =>
    cases i with
    | all => simp [Box.contained] at h
    | finite a b =>
      have hh : c ≤ a ∧ b ≤ d := of_decide_eq_true h
      exact ⟨(by exact_mod_cast hh.1 : (c:ℝ) ≤ (a:ℝ)).trans hx.1,
        hx.2.trans (by exact_mod_cast hh.2)⟩

def Box.positive : Box → Bool
  | .all => false
  | .finite a _ => decide (0 < a)

theorem pos_of_mem {i : Box} {x : ℝ} (hx : i.Mem x) (h : i.positive = true) :
    0 < x := by
  cases i with
  | all => simp [Box.positive] at h
  | finite a b =>
    have ha : (0:ℤ) < a := of_decide_eq_true h
    have haR : (0:ℝ) < (a:ℝ) := by exact_mod_cast ha
    nlinarith only [hx.1,haR,scale_pos]

/-- Multiply by an exact nonnegative rational, with one outward rounding.
Its domain condition is explicit in `mem_mulNonnegRat`. -/
def Box.mulNonnegRat : Box → ℚ → Box
  | .all,_ => .all
  | .finite a b,w => .finite (intFloor (a*w.num) w.den) (intCeil (b*w.num) w.den)

theorem mem_mulNonnegRat {i : Box} {x : ℝ} (hx : i.Mem x) {w : ℚ} (hw : 0 ≤ w) :
    (i.mulNonnegRat w).Mem (x*(w:ℝ)) := by
  cases i with
  | all => trivial
  | finite a b =>
    have hwR : (0:ℝ) ≤ (w:ℝ) := by exact_mod_cast hw
    have hd : (0:ℤ) < (w.den:ℤ) := by exact_mod_cast w.pos
    have hdR : (0:ℝ) < (w.den:ℝ) := by exact_mod_cast w.pos
    have hl : (intFloor (a*w.num) w.den:ℝ)*(w.den:ℝ) ≤ (a:ℝ)*(w.num:ℝ) := by
      exact_mod_cast floor_mul_le (a*w.num) hd
    have hu : (b:ℝ)*(w.num:ℝ) ≤ (intCeil (b*w.num) w.den:ℝ)*(w.den:ℝ) := by
      exact_mod_cast le_ceil_mul (b*w.num) hd
    have hl' : (intFloor (a*w.num) w.den:ℝ) ≤ (a:ℝ)*(w:ℝ) := by
      rw [Rat.cast_def,← mul_div_assoc]
      exact (le_div_iff₀ hdR).mpr hl
    have hu' : (b:ℝ)*(w:ℝ) ≤ (intCeil (b*w.num) w.den:ℝ) := by
      rw [Rat.cast_def,← mul_div_assoc]
      exact (div_le_iff₀ hdR).mpr hu
    have h1 := mul_le_mul_of_nonneg_right hx.1 hwR
    have h2 := mul_le_mul_of_nonneg_right hx.2 hwR
    change (intFloor (a*w.num) w.den:ℝ) ≤ (intervalScale:ℝ)*(x*(w:ℝ)) ∧
      (intervalScale:ℝ)*(x*(w:ℝ)) ≤ (intCeil (b*w.num) w.den:ℝ)
    constructor <;> nlinarith only [hl',hu',h1,h2]

end CarryIntegralCertificate
