import SigmaC5M2TaylorStateStage15Certificate

open CarrySigmaObstruction ZetaLean ZetaLean.ComplexInterval

#eval do
  let state15 := c5M2Stage15
  let state16 := c5RoundedExpStateC 896 c5M2TaylorArgExport 16
  let term16 := (ComplexInterval.smulQ (1 / (Nat.factorial 15 : ℚ)) state15.1).coarsen 896
  IO.println s!"power.lo={state16.1.re.lo}"
  IO.println s!"power.hi={state16.1.re.hi}"
  IO.println s!"term.lo={term16.re.lo}"
  IO.println s!"term.hi={term16.re.hi}"
  IO.println s!"sum.lo={state16.2.re.lo}"
  IO.println s!"sum.hi={state16.2.re.hi}"
