import SigmaC5ZeroExpStage5Certificate

open CarrySigmaObstruction ZetaLean ZetaLean.ComplexInterval

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option exponentiation.threshold 1024

def c5ZeroExpStage5Square : ComplexInterval :=
  c5ZeroExpStage5Export.mul c5ZeroExpStage5Export

def c5ZeroExpStage6Export : ComplexInterval := {
  re := {
    lo := (c5ZeroExpStage4Grid - 47) / c5ZeroExpStage4Grid
    hi := (c5ZeroExpStage4Grid + 63) / c5ZeroExpStage4Grid
    le := by norm_num [c5ZeroExpStage4Grid]
  }
  im := {
    lo := -63 / c5ZeroExpStage4Grid
    hi := 63 / c5ZeroExpStage4Grid
    le := by norm_num [c5ZeroExpStage4Grid]
  }
}

lemma c5ZeroExpStage5Square_re_lo_eq :
    c5ZeroExpStage5Square.re.lo =
      (c5ZeroExpStage4Grid ^ 2 - 46 * c5ZeroExpStage4Grid - 432) /
        c5ZeroExpStage4Grid ^ 2 := by
  norm_num [c5ZeroExpStage4Grid, c5ZeroExpStage5Square, ComplexInterval.mul,
    Interval.mul, Interval.sub, Interval.neg, Interval.add,
    c5ZeroExpStage5Export]

lemma c5ZeroExpStage5Square_re_hi_eq :
    c5ZeroExpStage5Square.re.hi =
      (c5ZeroExpStage4Grid ^ 2 + 62 * c5ZeroExpStage4Grid + 1922) /
        c5ZeroExpStage4Grid ^ 2 := by
  norm_num [c5ZeroExpStage4Grid, c5ZeroExpStage5Square, ComplexInterval.mul,
    Interval.mul, Interval.sub, Interval.neg, Interval.add,
    c5ZeroExpStage5Export]

lemma c5ZeroExpStage5Square_im_lo_eq :
    c5ZeroExpStage5Square.im.lo =
      (-62 * c5ZeroExpStage4Grid - 1922) / c5ZeroExpStage4Grid ^ 2 := by
  norm_num [c5ZeroExpStage4Grid, c5ZeroExpStage5Square, ComplexInterval.mul,
    Interval.mul, Interval.add, c5ZeroExpStage5Export]

lemma c5ZeroExpStage5Square_im_hi_eq :
    c5ZeroExpStage5Square.im.hi =
      (62 * c5ZeroExpStage4Grid + 1922) / c5ZeroExpStage4Grid ^ 2 := by
  norm_num [c5ZeroExpStage4Grid, c5ZeroExpStage5Square, ComplexInterval.mul,
    Interval.mul, Interval.add, c5ZeroExpStage5Export]

lemma c5ZeroExpStage5Square_re_lo_floor :
    Int.floor (c5ZeroExpStage5Square.re.lo * 2 ^ 896) = (2 : ℤ) ^ 896 - 47 := by
  rw [c5ZeroExpStage5Square_re_lo_eq]
  apply Int.floor_eq_iff.mpr
  constructor <;> norm_num [c5ZeroExpStage4Grid]

lemma c5ZeroExpStage5Square_re_hi_ceil :
    Int.ceil (c5ZeroExpStage5Square.re.hi * 2 ^ 896) = (2 : ℤ) ^ 896 + 63 := by
  rw [c5ZeroExpStage5Square_re_hi_eq]
  apply Int.ceil_eq_iff.mpr
  constructor <;> norm_num [c5ZeroExpStage4Grid]

lemma c5ZeroExpStage5Square_im_lo_floor :
    Int.floor (c5ZeroExpStage5Square.im.lo * 2 ^ 896) = -63 := by
  rw [c5ZeroExpStage5Square_im_lo_eq]
  apply Int.floor_eq_iff.mpr
  constructor <;> norm_num [c5ZeroExpStage4Grid]

lemma c5ZeroExpStage5Square_im_hi_ceil :
    Int.ceil (c5ZeroExpStage5Square.im.hi * 2 ^ 896) = 63 := by
  rw [c5ZeroExpStage5Square_im_hi_eq]
  apply Int.ceil_eq_iff.mpr
  constructor <;> norm_num [c5ZeroExpStage4Grid]

theorem c5ZeroExpStage6_eq :
    c5RoundedExpC 192 896 6 (ComplexInterval.exact 0 0) =
      c5ZeroExpStage6Export := by
  have hhalf : ComplexInterval.halveC (ComplexInterval.exact 0 0) =
      ComplexInterval.exact 0 0 := by
    simp [ComplexInterval.halveC, ComplexInterval.exact, Interval.exact,
      Interval.halve]
  have hy : c5RoundedExpC 192 896 5
      (ComplexInterval.halveC (ComplexInterval.exact 0 0)) =
      c5ZeroExpStage5Export := by
    rw [hhalf]
    simpa [c5RoundedExpC] using c5ZeroExpStage5_eq
  change ((c5RoundedExpC 192 896 5
      (ComplexInterval.halveC (ComplexInterval.exact 0 0))).mul
      (c5RoundedExpC 192 896 5
        (ComplexInterval.halveC (ComplexInterval.exact 0 0)))).coarsen 896 =
      c5ZeroExpStage6Export
  rw [hy]
  change c5ZeroExpStage5Square.coarsen 896 = c5ZeroExpStage6Export
  simp [ComplexInterval.coarsen, Interval.coarsen,
    c5ZeroExpStage5Square_re_lo_floor, c5ZeroExpStage5Square_re_hi_ceil,
    c5ZeroExpStage5Square_im_lo_floor, c5ZeroExpStage5Square_im_hi_ceil,
    c5ZeroExpStage6Export]
  norm_num [c5ZeroExpStage6Export, c5ZeroExpStage4Grid]
