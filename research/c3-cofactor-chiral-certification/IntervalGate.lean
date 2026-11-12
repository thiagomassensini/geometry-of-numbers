import CofactorIdentity
import Mathlib.Data.Real.Basic

namespace C3Cofactor

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 65536

/-- A rational center and a rational absolute error radius. This small interval
type is sufficient for the cofactor gate and keeps the calculation independent
of the analytic certificate that must later prove the input boxes. -/
structure RationalBall where
  center : ℚ
  radius : ℚ
  deriving DecidableEq, Repr

def RationalBall.Contains (a : RationalBall) (x : ℝ) : Prop :=
  |x - (a.center : ℝ)| ≤ (a.radius : ℝ)

def RationalBall.point (q : ℚ) : RationalBall := ⟨q, 0⟩
def RationalBall.add (a b : RationalBall) : RationalBall :=
  ⟨a.center + b.center, a.radius + b.radius⟩
def RationalBall.neg (a : RationalBall) : RationalBall := ⟨-a.center, a.radius⟩
def RationalBall.sub (a b : RationalBall) : RationalBall := a.add b.neg
def RationalBall.mul (a b : RationalBall) : RationalBall :=
  ⟨a.center * b.center,
    (|a.center| + a.radius) * b.radius + |b.center| * a.radius⟩

theorem RationalBall.point_contains (q : ℚ) :
    (RationalBall.point q).Contains (q : ℝ) := by
  simp [RationalBall.Contains, RationalBall.point]

theorem RationalBall.add_contains {a b : RationalBall} {x y : ℝ}
    (hx : a.Contains x) (hy : b.Contains y) :
    (a.add b).Contains (x + y) := by
  have hxa : 0 ≤ (a.radius : ℝ) := (abs_nonneg _).trans hx
  have hyb : 0 ≤ (b.radius : ℝ) := (abs_nonneg _).trans hy
  change |x + y - ((a.center + b.center : ℚ) : ℝ)| ≤ ((a.radius + b.radius : ℚ) : ℝ)
  have heq : x + y - ((a.center + b.center : ℚ) : ℝ) =
      (x - (a.center : ℝ)) + (y - (b.center : ℝ)) := by push_cast; ring
  rw [heq]
  calc
    _ ≤ |x - (a.center : ℝ)| + |y - (b.center : ℝ)| := abs_add_le _ _
    _ ≤ (a.radius : ℝ) + (b.radius : ℝ) := add_le_add hx hy
    _ = ((a.radius + b.radius : ℚ) : ℝ) := by push_cast; rfl

theorem RationalBall.neg_contains {a : RationalBall} {x : ℝ}
    (hx : a.Contains x) :
    a.neg.Contains (-x) := by
  change |-x - ((-a.center : ℚ) : ℝ)| ≤ (a.radius : ℝ)
  rw [show -x - ((-a.center : ℚ) : ℝ) = -(x - (a.center : ℝ)) by push_cast; ring,
    abs_neg]
  exact hx

theorem RationalBall.sub_contains {a b : RationalBall} {x y : ℝ}
    (hx : a.Contains x) (hy : b.Contains y) :
    (a.sub b).Contains (x - y) := by
  simpa only [RationalBall.sub, sub_eq_add_neg] using
    RationalBall.add_contains hx (RationalBall.neg_contains hy)

theorem RationalBall.mul_contains {a b : RationalBall} {x y : ℝ}
    (hx : a.Contains x) (hy : b.Contains y) :
    (a.mul b).Contains (x * y) := by
  have hra : 0 ≤ (a.radius : ℝ) := (abs_nonneg _).trans hx
  have hrb : 0 ≤ (b.radius : ℝ) := (abs_nonneg _).trans hy
  have hxnorm : |x| ≤ |(a.center : ℝ)| + (a.radius : ℝ) := by
    have heq : x = (x - (a.center : ℝ)) + (a.center : ℝ) := by ring
    rw [heq]
    calc
      _ ≤ |x - (a.center : ℝ)| + |(a.center : ℝ)| := abs_add_le _ _
      _ ≤ (a.radius : ℝ) + |(a.center : ℝ)| := add_le_add hx le_rfl
      _ = _ := by ring
  have heq : x * y - ((a.center * b.center : ℚ) : ℝ) =
      x * (y - (b.center : ℝ)) + (b.center : ℝ) * (x - (a.center : ℝ)) := by
    push_cast
    ring
  change |x * y - ((a.center * b.center : ℚ) : ℝ)| ≤
    (((|a.center| + a.radius) * b.radius + |b.center| * a.radius : ℚ) : ℝ)
  rw [heq]
  calc
    _ ≤ |x * (y - (b.center : ℝ))| + |(b.center : ℝ) * (x - (a.center : ℝ))| :=
      abs_add_le _ _
    _ = |x| * |y - (b.center : ℝ)| + |(b.center : ℝ)| * |x - (a.center : ℝ)| := by
      rw [abs_mul, abs_mul]
    _ ≤ (|(a.center : ℝ)| + (a.radius : ℝ)) * (b.radius : ℝ) +
        |(b.center : ℝ)| * (a.radius : ℝ) := by
      exact add_le_add
        (mul_le_mul hxnorm hy (abs_nonneg _) (by positivity))
        (mul_le_mul le_rfl hx (abs_nonneg _) (abs_nonneg _))
    _ = (((|a.center| + a.radius) * b.radius + |b.center| * a.radius : ℚ) : ℝ) := by
      push_cast
      ring

def candidateCoefficientBall (j : Fin 7) : RationalBall :=
  match j.val with
  | 0 => ⟨6214009727353926373909671746067469 / 12500000000000000000000000000000000, 2 / 10^12⟩
  | 1 => ⟨-5742986078786359383812469124408031 / 500000000000000000000000000000000000, 2 / 10^12⟩
  | 2 => ⟨6172600903515900344517289574864817 / 50000000000000000000000000000000000000, 1 / 10^15⟩
  | 3 => ⟨-83235548138552707200475872782457979 / 100000000000000000000000000000000000000000, 1 / 10^16⟩
  | 4 => ⟨39922265513441371747252703823393767 / 10000000000000000000000000000000000000000000, 1 / 10^20⟩
  | 5 => ⟨-14616025760110960862411857883057739 / 1000000000000000000000000000000000000000000000, 1 / 10^20⟩
  | 6 => ⟨42745400455368449576641221192081631 / 1000000000000000000000000000000000000000000000000, 1 / 10^20⟩
  | _ => RationalBall.point 0

def refXBall : RationalBall := RationalBall.point (14879782871 / 10^14)
def refYBall : RationalBall := RationalBall.point (1692226107996 / 10^14)

def oddABall : RationalBall :=
  RationalBall.sub (RationalBall.mul (candidateCoefficientBall 1) (candidateCoefficientBall 1))
    (RationalBall.mul (RationalBall.point 2)
      (RationalBall.mul (candidateCoefficientBall 0) (candidateCoefficientBall 2)))

def oddBBall : RationalBall :=
  RationalBall.sub (RationalBall.mul (candidateCoefficientBall 1) (candidateCoefficientBall 2))
    (RationalBall.mul (RationalBall.point 3)
      (RationalBall.mul (candidateCoefficientBall 0) (candidateCoefficientBall 3)))

def oddDBall : RationalBall :=
  RationalBall.sub (RationalBall.sub
    (RationalBall.mul (RationalBall.point 2)
      (RationalBall.mul (candidateCoefficientBall 2) (candidateCoefficientBall 2)))
    (RationalBall.mul (RationalBall.point 2)
      (RationalBall.mul (candidateCoefficientBall 1) (candidateCoefficientBall 3))))
    (RationalBall.mul (RationalBall.point 4)
      (RationalBall.mul (candidateCoefficientBall 0) (candidateCoefficientBall 4)))

def oddEBall : RationalBall :=
  RationalBall.sub (RationalBall.mul (candidateCoefficientBall 1) (candidateCoefficientBall 3))
    (RationalBall.mul (RationalBall.point 4)
      (RationalBall.mul (candidateCoefficientBall 0) (candidateCoefficientBall 4)))

def oddFBall : RationalBall :=
  RationalBall.sub (RationalBall.sub
    (RationalBall.mul (RationalBall.point 2)
      (RationalBall.mul (candidateCoefficientBall 2) (candidateCoefficientBall 3)))
    (RationalBall.mul (RationalBall.point 3)
      (RationalBall.mul (candidateCoefficientBall 1) (candidateCoefficientBall 4))))
    (RationalBall.mul (RationalBall.point 5)
      (RationalBall.mul (candidateCoefficientBall 0) (candidateCoefficientBall 5)))

def oddGBall : RationalBall :=
  RationalBall.sub (RationalBall.sub (RationalBall.sub
    (RationalBall.mul (RationalBall.point 3)
      (RationalBall.mul (candidateCoefficientBall 3) (candidateCoefficientBall 3)))
    (RationalBall.mul (RationalBall.point 2)
      (RationalBall.mul (candidateCoefficientBall 2) (candidateCoefficientBall 4))))
    (RationalBall.mul (RationalBall.point 4)
      (RationalBall.mul (candidateCoefficientBall 1) (candidateCoefficientBall 5))))
    (RationalBall.mul (RationalBall.point 6)
      (RationalBall.mul (candidateCoefficientBall 0) (candidateCoefficientBall 6)))

def oddPrefixBall : RationalBall :=
  RationalBall.sub (RationalBall.mul oddABall oddDBall) (RationalBall.mul oddBBall oddBBall)

def oddR0Ball : RationalBall :=
  RationalBall.add (RationalBall.add (RationalBall.mul oddABall refXBall)
    (RationalBall.mul oddBBall refYBall)) oddEBall

def oddR1Ball : RationalBall :=
  RationalBall.add (RationalBall.add (RationalBall.mul oddBBall refXBall)
    (RationalBall.mul oddDBall refYBall)) oddFBall

def oddEnergyBall : RationalBall :=
  RationalBall.add (RationalBall.add (RationalBall.add (RationalBall.add (RationalBall.add
    (RationalBall.mul oddABall (RationalBall.mul refXBall refXBall))
    (RationalBall.mul (RationalBall.point 2)
      (RationalBall.mul (RationalBall.mul oddBBall refXBall) refYBall)))
    (RationalBall.mul oddDBall (RationalBall.mul refYBall refYBall)))
    (RationalBall.mul (RationalBall.point 2) (RationalBall.mul oddEBall refXBall)))
    (RationalBall.mul (RationalBall.point 2) (RationalBall.mul oddFBall refYBall))) oddGBall

def oddAdjugateResidualBall : RationalBall :=
  RationalBall.add (RationalBall.sub
    (RationalBall.mul oddDBall (RationalBall.mul oddR0Ball oddR0Ball))
    (RationalBall.mul (RationalBall.point 2)
      (RationalBall.mul oddBBall (RationalBall.mul oddR0Ball oddR1Ball))))
    (RationalBall.mul oddABall (RationalBall.mul oddR1Ball oddR1Ball))

def oddCofactorMarginBall : RationalBall :=
  RationalBall.sub (RationalBall.mul oddPrefixBall oddEnergyBall) oddAdjugateResidualBall

theorem candidate_oddA_lower_positive :
    0 < oddABall.center - oddABall.radius := by
  norm_num [oddABall, candidateCoefficientBall, RationalBall.sub, RationalBall.add,
    RationalBall.mul, RationalBall.neg, RationalBall.point]

theorem candidate_oddPrefix_lower_positive :
    0 < oddPrefixBall.center - oddPrefixBall.radius := by
  norm_num [oddPrefixBall, oddABall, oddBBall, oddDBall, candidateCoefficientBall,
    RationalBall.sub, RationalBall.add, RationalBall.mul, RationalBall.neg,
    RationalBall.point]

theorem candidate_cofactor_margin_lower_positive :
    0 < oddCofactorMarginBall.center - oddCofactorMarginBall.radius := by
  norm_num [oddCofactorMarginBall, oddPrefixBall, oddABall, oddBBall, oddDBall,
    oddEBall, oddFBall, oddGBall, oddR0Ball, oddR1Ball, oddEnergyBall,
    oddAdjugateResidualBall, candidateCoefficientBall, refXBall, refYBall,
    RationalBall.sub, RationalBall.mul, RationalBall.add, RationalBall.neg,
    RationalBall.point]

end
end C3Cofactor
