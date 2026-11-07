import SigmaC5RationalNodeCenteredInstantiate

open CarrySigmaObstruction ZetaLean ZetaLean.ComplexInterval

def c5M2CenteredTermBox : ComplexInterval :=
  c5CenteredDirichletTermBox 512 192 896 4 2
    (ComplexInterval.exact (2 / 5) 0)

#eval do
  IO.println s!"re.lo={c5M2CenteredTermBox.re.lo}"
  IO.println s!"re.hi={c5M2CenteredTermBox.re.hi}"
  IO.println s!"im.lo={c5M2CenteredTermBox.im.lo}"
  IO.println s!"im.hi={c5M2CenteredTermBox.im.hi}"
