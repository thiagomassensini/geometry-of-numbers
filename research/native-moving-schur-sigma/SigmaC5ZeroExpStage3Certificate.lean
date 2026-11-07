import SigmaC5ZeroExpStagesCertificate

open CarrySigmaObstruction ZetaLean ZetaLean.ComplexInterval

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option exponentiation.threshold 1024

def c5ZeroExpStage2Square : ComplexInterval :=
  c5ZeroExpStage2Export.mul c5ZeroExpStage2Export

def c5ZeroExpStage3Grid : ℚ := 2 ^ 896

lemma c5ZeroExpStage2Square_re_lo_eq :
    c5ZeroExpStage2Square.re.lo =
      (c5ZeroExpStage3Grid ^ 2 - 4 * c5ZeroExpStage3Grid - 5) /
        c5ZeroExpStage3Grid ^ 2 := by
  norm_num [c5ZeroExpStage3Grid, c5ZeroExpStage2Square, ComplexInterval.mul,
    Interval.mul, Interval.sub, Interval.neg, Interval.add,
    c5ZeroExpStage2Export]

lemma c5ZeroExpStage2Square_re_hi_eq :
    c5ZeroExpStage2Square.re.hi =
      (c5ZeroExpStage3Grid ^ 2 + 6 * c5ZeroExpStage3Grid + 18) /
        c5ZeroExpStage3Grid ^ 2 := by
  norm_num [c5ZeroExpStage3Grid, c5ZeroExpStage2Square, ComplexInterval.mul,
    Interval.mul, Interval.sub, Interval.neg, Interval.add,
    c5ZeroExpStage2Export]

lemma c5ZeroExpStage2Square_im_lo_eq :
    c5ZeroExpStage2Square.im.lo =
      (-6 * c5ZeroExpStage3Grid - 18) / c5ZeroExpStage3Grid ^ 2 := by
  norm_num [c5ZeroExpStage3Grid, c5ZeroExpStage2Square, ComplexInterval.mul,
    Interval.mul, Interval.add, c5ZeroExpStage2Export]

lemma c5ZeroExpStage2Square_im_hi_eq :
    c5ZeroExpStage2Square.im.hi =
      (6 * c5ZeroExpStage3Grid + 18) / c5ZeroExpStage3Grid ^ 2 := by
  norm_num [c5ZeroExpStage3Grid, c5ZeroExpStage2Square, ComplexInterval.mul,
    Interval.mul, Interval.add, c5ZeroExpStage2Export]

lemma c5ZeroExpStage2Square_re_lo_floor :
    Int.floor (c5ZeroExpStage2Square.re.lo * 2 ^ 896) = (2 : ℤ) ^ 896 - 5 := by
  rw [c5ZeroExpStage2Square_re_lo_eq]
  apply Int.floor_eq_iff.mpr
  constructor <;> norm_num [c5ZeroExpStage3Grid]

lemma c5ZeroExpStage2Square_re_hi_ceil :
    Int.ceil (c5ZeroExpStage2Square.re.hi * 2 ^ 896) = (2 : ℤ) ^ 896 + 7 := by
  rw [c5ZeroExpStage2Square_re_hi_eq]
  apply Int.ceil_eq_iff.mpr
  constructor <;> norm_num [c5ZeroExpStage3Grid]

lemma c5ZeroExpStage2Square_im_lo_floor :
    Int.floor (c5ZeroExpStage2Square.im.lo * 2 ^ 896) = -7 := by
  rw [c5ZeroExpStage2Square_im_lo_eq]
  apply Int.floor_eq_iff.mpr
  constructor <;> norm_num [c5ZeroExpStage3Grid]

lemma c5ZeroExpStage2Square_im_hi_ceil :
    Int.ceil (c5ZeroExpStage2Square.im.hi * 2 ^ 896) = 7 := by
  rw [c5ZeroExpStage2Square_im_hi_eq]
  apply Int.ceil_eq_iff.mpr
  constructor <;> norm_num [c5ZeroExpStage3Grid]

theorem c5ZeroExpStage3_eq :
    c5RoundedExpC 192 896 3 (ComplexInterval.exact 0 0) =
      c5ZeroExpStage3Export := by
  have hhalf : ComplexInterval.halveC (ComplexInterval.exact 0 0) =
      ComplexInterval.exact 0 0 := by
    simp [ComplexInterval.halveC, ComplexInterval.exact, Interval.exact,
      Interval.halve]
  have hy : c5RoundedExpC 192 896 2
      (ComplexInterval.halveC (ComplexInterval.exact 0 0)) =
      c5ZeroExpStage2Export := by
    rw [hhalf]
    simpa [c5RoundedExpC] using c5ZeroExpStage2_eq
  change ((c5RoundedExpC 192 896 2
      (ComplexInterval.halveC (ComplexInterval.exact 0 0))).mul
      (c5RoundedExpC 192 896 2
        (ComplexInterval.halveC (ComplexInterval.exact 0 0)))).coarsen 896 =
      c5ZeroExpStage3Export
  rw [hy]
  change c5ZeroExpStage2Square.coarsen 896 = c5ZeroExpStage3Export
  simp [ComplexInterval.coarsen, Interval.coarsen,
    c5ZeroExpStage2Square_re_lo_floor, c5ZeroExpStage2Square_re_hi_ceil,
    c5ZeroExpStage2Square_im_lo_floor, c5ZeroExpStage2Square_im_hi_ceil,
    c5ZeroExpStage3Export]
  norm_num [c5ZeroExpStage3Export]
