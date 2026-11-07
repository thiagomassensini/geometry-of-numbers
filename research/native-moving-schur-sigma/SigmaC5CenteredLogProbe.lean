import SigmaC5RationalNodeCenteredBoxes

open ZetaLean

def c5CenteredLogProbeBox : Interval :=
  (CarrySigmaObstruction.c5CenteredLogQ 512
    (CarrySigmaObstruction.c5CenteredLogScale 100) 100).coarsen 896

def c5CenteredLogProbeWidth : ℚ := c5CenteredLogProbeBox.hi - c5CenteredLogProbeBox.lo

#eval (c5CenteredLogProbeWidth.num.natAbs.log2, c5CenteredLogProbeWidth.den.log2)
