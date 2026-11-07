import SigmaC5RationalNodeCenteredBoxes

open ZetaLean ZetaLean.ComplexInterval

def c5CenteredProbeBox : ComplexInterval :=
  CarrySigmaObstruction.c5CenteredDirichletTermBox 512 192 896 4 100
    (ComplexInterval.exact (2 / 5) (128 / 100000))

def c5CenteredProbeRealWidth : ℚ := c5CenteredProbeBox.re.hi - c5CenteredProbeBox.re.lo
def c5CenteredProbeImagWidth : ℚ := c5CenteredProbeBox.im.hi - c5CenteredProbeBox.im.lo

#eval (c5CenteredProbeRealWidth.num.natAbs.log2, c5CenteredProbeRealWidth.den.log2)
#eval (c5CenteredProbeImagWidth.num.natAbs.log2, c5CenteredProbeImagWidth.den.log2)
