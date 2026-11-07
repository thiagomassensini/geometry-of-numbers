import SigmaC5RationalNodeCenteredBoxes

open ZetaLean ZetaLean.ComplexInterval
open CarrySigmaObstruction

def c5RoundedTermProbeBox : ComplexInterval :=
  c5CenteredDirichletTermBoxWithLogTwo 512 192 896 4 (c5CenteredLog2I 512) 100
    (ComplexInterval.exact (3 / 5) (128 / 100000))

def c5RoundedTermProbeRealWidth : ℚ :=
  c5RoundedTermProbeBox.re.hi - c5RoundedTermProbeBox.re.lo

def c5RoundedTermProbeImagWidth : ℚ :=
  c5RoundedTermProbeBox.im.hi - c5RoundedTermProbeBox.im.lo

#eval ((c5RoundedTermProbeRealWidth.num.natAbs.log2,
    c5RoundedTermProbeRealWidth.den.log2),
  (c5RoundedTermProbeImagWidth.num.natAbs.log2,
    c5RoundedTermProbeImagWidth.den.log2))
