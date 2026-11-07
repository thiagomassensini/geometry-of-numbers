import SigmaC5ZeroExpStage3Certificate

open CarrySigmaObstruction ZetaLean ZetaLean.ComplexInterval

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option exponentiation.threshold 1024

def c5ZeroExpStage3Square : ComplexInterval :=
  c5ZeroExpStage3Export.mul c5ZeroExpStage3Export

def c5ZeroExpStage4Grid : ℚ := 2 ^ 896

lemma c5ZeroExpStage3Square_re_lo_eq :
    c5ZeroExpStage3Square.re.lo =
      (c5ZeroExpStage4Grid ^ 2 - 10 * c5ZeroExpStage4Grid - 24) /
        c5ZeroExpStage4Grid ^ 2 := by
  norm_num [c5ZeroExpStage4Grid, c5ZeroExpStage3Square, ComplexInterval.mul,
    Interval.mul, Interval.sub, Interval.neg, Interval.add,
    c5ZeroExpStage3Export]

lemma c5ZeroExpStage3Square_re_hi_eq :
    c5ZeroExpStage3Square.re.hi =
      (c5ZeroExpStage4Grid ^ 2 + 14 * c5ZeroExpStage4Grid + 98) /
        c5ZeroExpStage4Grid ^ 2 := by
  norm_num [c5ZeroExpStage4Grid, c5ZeroExpStage3Square, ComplexInterval.mul,
    Interval.mul, Interval.sub, Interval.neg, Interval.add,
    c5ZeroExpStage3Export]

lemma c5ZeroExpStage3Square_im_lo_eq :
    c5ZeroExpStage3Square.im.lo =
      (-14 * c5ZeroExpStage4Grid - 98) / c5ZeroExpStage4Grid ^ 2 := by
  norm_num [c5ZeroExpStage4Grid, c5ZeroExpStage3Square, ComplexInterval.mul,
    Interval.mul, Interval.add, c5ZeroExpStage3Export]

lemma c5ZeroExpStage3Square_im_hi_eq :
    c5ZeroExpStage3Square.im.hi =
      (14 * c5ZeroExpStage4Grid + 98) / c5ZeroExpStage4Grid ^ 2 := by
  norm_num [c5ZeroExpStage4Grid, c5ZeroExpStage3Square, ComplexInterval.mul,
    Interval.mul, Interval.add, c5ZeroExpStage3Export]

lemma c5ZeroExpStage3Square_re_lo_floor :
    Int.floor (c5ZeroExpStage3Square.re.lo * 2 ^ 896) = (2 : ℤ) ^ 896 - 11 := by
  rw [c5ZeroExpStage3Square_re_lo_eq]
  apply Int.floor_eq_iff.mpr
  constructor <;> norm_num [c5ZeroExpStage4Grid]

lemma c5ZeroExpStage3Square_re_hi_ceil :
    Int.ceil (c5ZeroExpStage3Square.re.hi * 2 ^ 896) = (2 : ℤ) ^ 896 + 15 := by
  rw [c5ZeroExpStage3Square_re_hi_eq]
  apply Int.ceil_eq_iff.mpr
  constructor <;> norm_num [c5ZeroExpStage4Grid]

lemma c5ZeroExpStage3Square_im_lo_floor :
    Int.floor (c5ZeroExpStage3Square.im.lo * 2 ^ 896) = -15 := by
  rw [c5ZeroExpStage3Square_im_lo_eq]
  apply Int.floor_eq_iff.mpr
  constructor <;> norm_num [c5ZeroExpStage4Grid]

lemma c5ZeroExpStage3Square_im_hi_ceil :
    Int.ceil (c5ZeroExpStage3Square.im.hi * 2 ^ 896) = 15 := by
  rw [c5ZeroExpStage3Square_im_hi_eq]
  apply Int.ceil_eq_iff.mpr
  constructor <;> norm_num [c5ZeroExpStage4Grid]

theorem c5ZeroExpStage4_eq :
    c5RoundedExpC 192 896 4 (ComplexInterval.exact 0 0) =
      c5ZeroExpStage4Export := by
  have hhalf : ComplexInterval.halveC (ComplexInterval.exact 0 0) =
      ComplexInterval.exact 0 0 := by
    simp [ComplexInterval.halveC, ComplexInterval.exact, Interval.exact,
      Interval.halve]
  have hy : c5RoundedExpC 192 896 3
      (ComplexInterval.halveC (ComplexInterval.exact 0 0)) =
      c5ZeroExpStage3Export := by
    rw [hhalf]
    simpa [c5RoundedExpC] using c5ZeroExpStage3_eq
  change ((c5RoundedExpC 192 896 3
      (ComplexInterval.halveC (ComplexInterval.exact 0 0))).mul
      (c5RoundedExpC 192 896 3
        (ComplexInterval.halveC (ComplexInterval.exact 0 0)))).coarsen 896 =
      c5ZeroExpStage4Export
  rw [hy]
  change c5ZeroExpStage3Square.coarsen 896 = c5ZeroExpStage4Export
  simp [ComplexInterval.coarsen, Interval.coarsen,
    c5ZeroExpStage3Square_re_lo_floor, c5ZeroExpStage3Square_re_hi_ceil,
    c5ZeroExpStage3Square_im_lo_floor, c5ZeroExpStage3Square_im_hi_ceil,
    c5ZeroExpStage4Export]
  norm_num [c5ZeroExpStage4Export]
