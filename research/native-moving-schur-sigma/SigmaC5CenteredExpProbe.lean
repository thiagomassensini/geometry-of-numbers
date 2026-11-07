import SigmaC5RationalNodeCenteredBoxes

open ZetaLean ZetaLean.ComplexInterval

def c5CenteredExpProbeInput : ComplexInterval :=
  (ComplexInterval.exact (2 / 5) (128 / 100000)).neg.mul
    { re := (CarrySigmaObstruction.c5CenteredLogQ 512
      (CarrySigmaObstruction.c5CenteredLogScale 100) 100).coarsen 896,
      im := Interval.exact 0 }

def c5CenteredExpProbeBox : ComplexInterval :=
  expCr 192 896 4 c5CenteredExpProbeInput

def c5CenteredExpProbeRealWidth : ℚ :=
  c5CenteredExpProbeBox.re.hi - c5CenteredExpProbeBox.re.lo

def c5CenteredExpProbeImagWidth : ℚ :=
  c5CenteredExpProbeBox.im.hi - c5CenteredExpProbeBox.im.lo

#eval (c5CenteredExpProbeRealWidth.num.natAbs.log2, c5CenteredExpProbeRealWidth.den.log2)
#eval (c5CenteredExpProbeImagWidth.num.natAbs.log2, c5CenteredExpProbeImagWidth.den.log2)
