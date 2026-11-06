import SigmaFiniteCoefficientSignTransport

/-!
# Exact rational ball arithmetic for finite C2 coefficient boxes

This file formalizes only the propagation of rational coefficient enclosures.
It does not assert that the original source coefficients lie in the supplied
boxes; that analytic inclusion remains a separate obligation.
-/

namespace CarrySigmaObstruction

noncomputable section
set_option autoImplicit false

/-- A rational ball stores its midpoint and radius. -/
abbrev SigmaRatBall := ℚ × ℚ

def sigmaRatBallValid (a : SigmaRatBall) : Prop := 0 ≤ a.2

def sigmaRatBallContains (a : SigmaRatBall) (x : ℝ) : Prop :=
  |x - (a.1 : ℝ)| ≤ (a.2 : ℝ)

def sigmaRatBallConst (q : ℚ) : SigmaRatBall := (q, 0)

def sigmaRatBallNeg (a : SigmaRatBall) : SigmaRatBall := (-a.1, a.2)

/-- The product radius follows from `xy-ab = a(y-b)+b(x-a)+(x-a)(y-b)`. -/
def sigmaRatBallMul (a b : SigmaRatBall) : SigmaRatBall :=
  (a.1 * b.1, |a.1| * b.2 + |b.1| * a.2 + a.2 * b.2)

def sigmaRatBallPow (a : SigmaRatBall) : ℕ → SigmaRatBall
  | 0 => sigmaRatBallConst 1
  | n + 1 => sigmaRatBallMul (sigmaRatBallPow a n) a

theorem sigmaRatBallConst_valid (q : ℚ) : sigmaRatBallValid (sigmaRatBallConst q) := by
  simp [sigmaRatBallValid, sigmaRatBallConst]

theorem sigmaRatBallNeg_valid {a : SigmaRatBall} (ha : sigmaRatBallValid a) :
    sigmaRatBallValid (sigmaRatBallNeg a) := by
  exact ha

theorem sigmaRatBallAdd_valid {a b : SigmaRatBall}
    (ha : sigmaRatBallValid a) (hb : sigmaRatBallValid b) :
    sigmaRatBallValid (a + b) := by
  exact add_nonneg ha hb

theorem sigmaRatBallMul_valid {a b : SigmaRatBall}
    (ha : sigmaRatBallValid a) (hb : sigmaRatBallValid b) :
    sigmaRatBallValid (sigmaRatBallMul a b) := by
  change 0 ≤ a.2 at ha
  change 0 ≤ b.2 at hb
  simp [sigmaRatBallValid, sigmaRatBallMul]
  positivity

theorem sigmaRatBallContains_add {a b : SigmaRatBall} {x y : ℝ}
    (hx : sigmaRatBallContains a x) (hy : sigmaRatBallContains b y) :
    sigmaRatBallContains (a + b) (x + y) := by
  change |x + y - ((a.1 + b.1 : ℚ) : ℝ)| ≤ ((a.2 + b.2 : ℚ) : ℝ)
  rw [show x + y - ((a.1 + b.1 : ℚ) : ℝ) =
      (x - (a.1 : ℝ)) + (y - (b.1 : ℝ)) by push_cast; ring]
  calc
    |(x - (a.1 : ℝ)) + (y - (b.1 : ℝ))| ≤
        |x - (a.1 : ℝ)| + |y - (b.1 : ℝ)| := abs_add_le _ _
    _ ≤ (a.2 : ℝ) + (b.2 : ℝ) := add_le_add hx hy
    _ = ((a.2 + b.2 : ℚ) : ℝ) := by push_cast; rfl

theorem sigmaRatBallContains_neg {a : SigmaRatBall} {x : ℝ}
    (hx : sigmaRatBallContains a x) :
    sigmaRatBallContains (sigmaRatBallNeg a) (-x) := by
  change |-x - ((-a.1 : ℚ) : ℝ)| ≤ (a.2 : ℝ)
  rw [show -x - ((-a.1 : ℚ) : ℝ) = -(x - (a.1 : ℝ)) by push_cast; ring,
    abs_neg]
  exact hx

theorem sigmaRatBallContains_mul {a b : SigmaRatBall} {x y : ℝ}
    (ha : sigmaRatBallValid a) (_hb : sigmaRatBallValid b)
    (hx : sigmaRatBallContains a x) (hy : sigmaRatBallContains b y) :
    sigmaRatBallContains (sigmaRatBallMul a b) (x * y) := by
  change |x * y - ((a.1 * b.1 : ℚ) : ℝ)| ≤
    ((|a.1| * b.2 + |b.1| * a.2 + a.2 * b.2 : ℚ) : ℝ)
  have hdecomp : x * y - ((a.1 * b.1 : ℚ) : ℝ) =
      (a.1 : ℝ) * (y - (b.1 : ℝ)) +
        (b.1 : ℝ) * (x - (a.1 : ℝ)) +
          (x - (a.1 : ℝ)) * (y - (b.1 : ℝ)) := by
    push_cast
    ring
  rw [hdecomp]
  have hfirst := abs_add_le ((a.1 : ℝ) * (y - (b.1 : ℝ)))
    ((b.1 : ℝ) * (x - (a.1 : ℝ)))
  have hsecond := abs_add_le
    ((a.1 : ℝ) * (y - (b.1 : ℝ)) + (b.1 : ℝ) * (x - (a.1 : ℝ)))
    ((x - (a.1 : ℝ)) * (y - (b.1 : ℝ)))
  have hA : |(a.1 : ℝ)| * |y - (b.1 : ℝ)| ≤
      |(a.1 : ℝ)| * (b.2 : ℝ) :=
    mul_le_mul_of_nonneg_left hy (abs_nonneg _)
  have hB : |(b.1 : ℝ)| * |x - (a.1 : ℝ)| ≤
      |(b.1 : ℝ)| * (a.2 : ℝ) :=
    mul_le_mul_of_nonneg_left hx (abs_nonneg _)
  have hx0 : 0 ≤ |x - (a.1 : ℝ)| := abs_nonneg _
  have ha0 : 0 ≤ (a.2 : ℝ) := by exact_mod_cast ha
  have hy0 : 0 ≤ |y - (b.1 : ℝ)| := abs_nonneg _
  have hab : |x - (a.1 : ℝ)| * |y - (b.1 : ℝ)| ≤
      (a.2 : ℝ) * (b.2 : ℝ) := mul_le_mul hx hy hy0 ha0
  have hsum :
      |(a.1 : ℝ) * (y - (b.1 : ℝ)) +
        (b.1 : ℝ) * (x - (a.1 : ℝ)) +
          (x - (a.1 : ℝ)) * (y - (b.1 : ℝ))| ≤
        |(a.1 : ℝ) * (y - (b.1 : ℝ))| +
          |(b.1 : ℝ) * (x - (a.1 : ℝ))| +
            |(x - (a.1 : ℝ)) * (y - (b.1 : ℝ))| := by
    linarith [hfirst, hsecond]
  calc
    |(a.1 : ℝ) * (y - (b.1 : ℝ)) +
        (b.1 : ℝ) * (x - (a.1 : ℝ)) +
          (x - (a.1 : ℝ)) * (y - (b.1 : ℝ))|
        ≤ |(a.1 : ℝ) * (y - (b.1 : ℝ))| +
          |(b.1 : ℝ) * (x - (a.1 : ℝ))| +
            |(x - (a.1 : ℝ)) * (y - (b.1 : ℝ))| := by
          exact hsum
    _ = |(a.1 : ℝ)| * |y - (b.1 : ℝ)| +
          |(b.1 : ℝ)| * |x - (a.1 : ℝ)| +
            |x - (a.1 : ℝ)| * |y - (b.1 : ℝ)| := by rw [abs_mul, abs_mul, abs_mul]
    _ ≤ |(a.1 : ℝ)| * (b.2 : ℝ) +
          |(b.1 : ℝ)| * (a.2 : ℝ) + (a.2 : ℝ) * (b.2 : ℝ) := by
          exact add_le_add (add_le_add hA hB) hab
    _ = ((|a.1| * b.2 + |b.1| * a.2 + a.2 * b.2 : ℚ) : ℝ) := by
          norm_cast

theorem sigmaRatBallPow_valid {a : SigmaRatBall} (ha : sigmaRatBallValid a) :
    ∀ n, sigmaRatBallValid (sigmaRatBallPow a n) := by
  intro n
  induction n with
  | zero => exact sigmaRatBallConst_valid 1
  | succ n ih => exact sigmaRatBallMul_valid ih ha

theorem sigmaRatBallContains_pow {a : SigmaRatBall} {x : ℝ}
    (ha : sigmaRatBallValid a) (hx : sigmaRatBallContains a x) :
    ∀ n, sigmaRatBallContains (sigmaRatBallPow a n) (x ^ n) := by
  intro n
  induction n with
  | zero =>
      simp [sigmaRatBallContains, sigmaRatBallPow, sigmaRatBallConst]
  | succ n ih =>
      simpa [sigmaRatBallPow, pow_succ] using
        sigmaRatBallContains_mul (sigmaRatBallPow_valid ha n) ha ih hx

end
end CarrySigmaObstruction
