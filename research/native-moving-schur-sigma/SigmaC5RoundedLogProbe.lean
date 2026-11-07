import SigmaC5RationalNodePreciseLogBounds

open ZetaLean

def c5RoundedLogProbeBox : Interval :=
  CarrySigmaObstruction.c5CenteredFastLog1 512 (Interval.exact (25 / 32))

def c5RoundedLogProbeWidth : ℚ :=
  c5RoundedLogProbeBox.hi - c5RoundedLogProbeBox.lo

#eval (c5RoundedLogProbeWidth.num.natAbs.log2, c5RoundedLogProbeWidth.den.log2)
