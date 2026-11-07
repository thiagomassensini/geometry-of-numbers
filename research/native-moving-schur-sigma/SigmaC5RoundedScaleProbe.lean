import SigmaC5RoundedRationalScale

open ZetaLean ZetaLean.ComplexInterval
open CarrySigmaObstruction

def c5RoundedScaleProbeBox : ComplexInterval :=
  c5RatScaleInterval 896 (3 / 5) (128 / 100000) 300 100

def c5RoundedScaleProbeRealWidth : ℚ :=
  c5RoundedScaleProbeBox.re.hi - c5RoundedScaleProbeBox.re.lo

def c5RoundedScaleProbeImagWidth : ℚ :=
  c5RoundedScaleProbeBox.im.hi - c5RoundedScaleProbeBox.im.lo

#eval ((c5RoundedScaleProbeRealWidth.num.natAbs.log2,
    c5RoundedScaleProbeRealWidth.den.log2),
  (c5RoundedScaleProbeImagWidth.num.natAbs.log2,
    c5RoundedScaleProbeImagWidth.den.log2))
