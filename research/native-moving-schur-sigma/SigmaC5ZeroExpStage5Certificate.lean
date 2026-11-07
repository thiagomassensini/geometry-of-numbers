import SigmaC5ZeroExpStage4Certificate

open CarrySigmaObstruction ZetaLean ZetaLean.ComplexInterval

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option exponentiation.threshold 1024

def c5ZeroExpStage4Square : ComplexInterval :=
  c5ZeroExpStage4Export.mul c5ZeroExpStage4Export

def c5ZeroExpStage5Export : ComplexInterval := {
  re := {
    lo := (c5ZeroExpStage4Grid - 23) / c5ZeroExpStage4Grid
    hi := (c5ZeroExpStage4Grid + 31) / c5ZeroExpStage4Grid
    le := by norm_num [c5ZeroExpStage4Grid]
  }
  im := {
    lo := -31 / c5ZeroExpStage4Grid
    hi := 31 / c5ZeroExpStage4Grid
    le := by norm_num [c5ZeroExpStage4Grid]
  }
}

lemma c5ZeroExpStage4Square_re_lo_eq :
    c5ZeroExpStage4Square.re.lo =
      (c5ZeroExpStage4Grid ^ 2 - 22 * c5ZeroExpStage4Grid - 104) /
        c5ZeroExpStage4Grid ^ 2 := by
  norm_num [c5ZeroExpStage4Grid, c5ZeroExpStage4Square, ComplexInterval.mul,
    Interval.mul, Interval.sub, Interval.neg, Interval.add,
    c5ZeroExpStage4Export]

lemma c5ZeroExpStage4Square_re_hi_eq :
    c5ZeroExpStage4Square.re.hi =
      (c5ZeroExpStage4Grid ^ 2 + 30 * c5ZeroExpStage4Grid + 450) /
        c5ZeroExpStage4Grid ^ 2 := by
  norm_num [c5ZeroExpStage4Grid, c5ZeroExpStage4Square, ComplexInterval.mul,
    Interval.mul, Interval.sub, Interval.neg, Interval.add,
    c5ZeroExpStage4Export]

lemma c5ZeroExpStage4Square_im_lo_eq :
    c5ZeroExpStage4Square.im.lo =
      (-30 * c5ZeroExpStage4Grid - 450) / c5ZeroExpStage4Grid ^ 2 := by
  norm_num [c5ZeroExpStage4Grid, c5ZeroExpStage4Square, ComplexInterval.mul,
    Interval.mul, Interval.add, c5ZeroExpStage4Export]

lemma c5ZeroExpStage4Square_im_hi_eq :
    c5ZeroExpStage4Square.im.hi =
      (30 * c5ZeroExpStage4Grid + 450) / c5ZeroExpStage4Grid ^ 2 := by
  norm_num [c5ZeroExpStage4Grid, c5ZeroExpStage4Square, ComplexInterval.mul,
    Interval.mul, Interval.add, c5ZeroExpStage4Export]

lemma c5ZeroExpStage4Square_re_lo_floor :
    Int.floor (c5ZeroExpStage4Square.re.lo * 2 ^ 896) = (2 : ℤ) ^ 896 - 23 := by
  rw [c5ZeroExpStage4Square_re_lo_eq]
  apply Int.floor_eq_iff.mpr
  constructor <;> norm_num [c5ZeroExpStage4Grid]

lemma c5ZeroExpStage4Square_re_hi_ceil :
    Int.ceil (c5ZeroExpStage4Square.re.hi * 2 ^ 896) = (2 : ℤ) ^ 896 + 31 := by
  rw [c5ZeroExpStage4Square_re_hi_eq]
  apply Int.ceil_eq_iff.mpr
  constructor <;> norm_num [c5ZeroExpStage4Grid]

lemma c5ZeroExpStage4Square_im_lo_floor :
    Int.floor (c5ZeroExpStage4Square.im.lo * 2 ^ 896) = -31 := by
  rw [c5ZeroExpStage4Square_im_lo_eq]
  apply Int.floor_eq_iff.mpr
  constructor <;> norm_num [c5ZeroExpStage4Grid]

lemma c5ZeroExpStage4Square_im_hi_ceil :
    Int.ceil (c5ZeroExpStage4Square.im.hi * 2 ^ 896) = 31 := by
  rw [c5ZeroExpStage4Square_im_hi_eq]
  apply Int.ceil_eq_iff.mpr
  constructor <;> norm_num [c5ZeroExpStage4Grid]

theorem c5ZeroExpStage5_eq :
    c5RoundedExpC 192 896 5 (ComplexInterval.exact 0 0) =
      c5ZeroExpStage5Export := by
  have hhalf : ComplexInterval.halveC (ComplexInterval.exact 0 0) =
      ComplexInterval.exact 0 0 := by
    simp [ComplexInterval.halveC, ComplexInterval.exact, Interval.exact,
      Interval.halve]
  have hy : c5RoundedExpC 192 896 4
      (ComplexInterval.halveC (ComplexInterval.exact 0 0)) =
      c5ZeroExpStage4Export := by
    rw [hhalf]
    simpa [c5RoundedExpC] using c5ZeroExpStage4_eq
  change ((c5RoundedExpC 192 896 4
      (ComplexInterval.halveC (ComplexInterval.exact 0 0))).mul
      (c5RoundedExpC 192 896 4
        (ComplexInterval.halveC (ComplexInterval.exact 0 0)))).coarsen 896 =
      c5ZeroExpStage5Export
  rw [hy]
  change c5ZeroExpStage4Square.coarsen 896 = c5ZeroExpStage5Export
  simp [ComplexInterval.coarsen, Interval.coarsen,
    c5ZeroExpStage4Square_re_lo_floor, c5ZeroExpStage4Square_re_hi_ceil,
    c5ZeroExpStage4Square_im_lo_floor, c5ZeroExpStage4Square_im_hi_ceil,
    c5ZeroExpStage5Export]
  norm_num [c5ZeroExpStage5Export, c5ZeroExpStage4Grid]
