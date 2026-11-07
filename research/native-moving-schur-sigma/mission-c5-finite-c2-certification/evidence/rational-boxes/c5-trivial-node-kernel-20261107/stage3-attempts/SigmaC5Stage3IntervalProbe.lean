import SigmaC5ZeroExpStagesCertificate

open CarrySigmaObstruction ZetaLean ZetaLean.ComplexInterval

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option exponentiation.threshold 1024

def c5Stage3ProbeD : ℚ := 2 ^ 896

def c5Stage3ProbeSquare : ComplexInterval :=
  c5ZeroExpStage2Export.mul c5ZeroExpStage2Export

example : c5Stage3ProbeSquare.re.lo =
    (c5Stage3ProbeD ^ 2 - 4 * c5Stage3ProbeD - 5) /
      c5Stage3ProbeD ^ 2 := by
  norm_num [c5Stage3ProbeD, c5Stage3ProbeSquare, ComplexInterval.mul,
    Interval.mul, Interval.sub, Interval.neg, Interval.add,
    c5ZeroExpStage2Export]

example : c5Stage3ProbeSquare.re.hi =
    (c5Stage3ProbeD ^ 2 + 6 * c5Stage3ProbeD + 18) /
      c5Stage3ProbeD ^ 2 := by
  norm_num [c5Stage3ProbeD, c5Stage3ProbeSquare, ComplexInterval.mul,
    Interval.mul, Interval.sub, Interval.neg, Interval.add,
    c5ZeroExpStage2Export]

example : c5Stage3ProbeSquare.im.lo =
    (-6 * c5Stage3ProbeD - 18) / c5Stage3ProbeD ^ 2 := by
  norm_num [c5Stage3ProbeD, c5Stage3ProbeSquare, ComplexInterval.mul,
    Interval.mul, Interval.add, c5ZeroExpStage2Export]

example : c5Stage3ProbeSquare.im.hi =
    (6 * c5Stage3ProbeD + 18) / c5Stage3ProbeD ^ 2 := by
  norm_num [c5Stage3ProbeD, c5Stage3ProbeSquare, ComplexInterval.mul,
    Interval.mul, Interval.add, c5ZeroExpStage2Export]

lemma c5Stage3Probe_re_lo_floor :
    Int.floor (c5Stage3ProbeSquare.re.lo * 2 ^ 896) = (2 : ℤ) ^ 896 - 5 := by
  rw [show c5Stage3ProbeSquare.re.lo =
      (c5Stage3ProbeD ^ 2 - 4 * c5Stage3ProbeD - 5) /
        c5Stage3ProbeD ^ 2 by
        norm_num [c5Stage3ProbeD, c5Stage3ProbeSquare, ComplexInterval.mul,
          Interval.mul, Interval.sub, Interval.neg, Interval.add,
          c5ZeroExpStage2Export]]
  apply Int.floor_eq_iff.mpr
  constructor <;> norm_num [c5Stage3ProbeD]

lemma c5Stage3Probe_re_hi_ceil :
    Int.ceil (c5Stage3ProbeSquare.re.hi * 2 ^ 896) = (2 : ℤ) ^ 896 + 7 := by
  rw [show c5Stage3ProbeSquare.re.hi =
      (c5Stage3ProbeD ^ 2 + 6 * c5Stage3ProbeD + 18) /
        c5Stage3ProbeD ^ 2 by
        norm_num [c5Stage3ProbeD, c5Stage3ProbeSquare, ComplexInterval.mul,
          Interval.mul, Interval.sub, Interval.neg, Interval.add,
          c5ZeroExpStage2Export]]
  apply Int.ceil_eq_iff.mpr
  constructor <;> norm_num [c5Stage3ProbeD]

lemma c5Stage3Probe_im_lo_floor :
    Int.floor (c5Stage3ProbeSquare.im.lo * 2 ^ 896) = -7 := by
  rw [show c5Stage3ProbeSquare.im.lo =
      (-6 * c5Stage3ProbeD - 18) / c5Stage3ProbeD ^ 2 by
        norm_num [c5Stage3ProbeD, c5Stage3ProbeSquare, ComplexInterval.mul,
          Interval.mul, Interval.add, c5ZeroExpStage2Export]]
  apply Int.floor_eq_iff.mpr
  constructor <;> norm_num [c5Stage3ProbeD]

lemma c5Stage3Probe_im_hi_ceil :
    Int.ceil (c5Stage3ProbeSquare.im.hi * 2 ^ 896) = 7 := by
  rw [show c5Stage3ProbeSquare.im.hi =
      (6 * c5Stage3ProbeD + 18) / c5Stage3ProbeD ^ 2 by
        norm_num [c5Stage3ProbeD, c5Stage3ProbeSquare, ComplexInterval.mul,
          Interval.mul, Interval.add, c5ZeroExpStage2Export]]
  apply Int.ceil_eq_iff.mpr
  constructor <;> norm_num [c5Stage3ProbeD]
