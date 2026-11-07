import SigmaC5RationalNodeCenteredInstantiate

open ZetaLean ZetaLean.ComplexInterval
open CarrySigmaObstruction

def c5CenteredNodeProbeBox : ComplexInterval :=
  c5RationalZetaCenteredNodeBox 512 192 896 (3 / 5) (128 / 100000)

def c5CenteredNodeProbeRealWidth : ℚ :=
  c5CenteredNodeProbeBox.re.hi - c5CenteredNodeProbeBox.re.lo

def c5CenteredNodeProbeImagWidth : ℚ :=
  c5CenteredNodeProbeBox.im.hi - c5CenteredNodeProbeBox.im.lo

#eval ((c5CenteredNodeProbeRealWidth.num.natAbs.log2,
    c5CenteredNodeProbeRealWidth.den.log2),
  (c5CenteredNodeProbeImagWidth.num.natAbs.log2,
    c5CenteredNodeProbeImagWidth.den.log2))
