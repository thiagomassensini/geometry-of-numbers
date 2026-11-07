import SigmaC5M2TaylorStateStage11Certificate

open CarrySigmaObstruction ZetaLean ZetaLean.ComplexInterval

#eval do
  let state11 := c5M2Stage11
  let state12 := c5RoundedExpStateC 896 c5M2TaylorArgExport 12
  let term12 := (ComplexInterval.smulQ (1 / (Nat.factorial 11 : ℚ)) state11.1).coarsen 896
  IO.println s!"power.lo={state12.1.re.lo}"
  IO.println s!"power.hi={state12.1.re.hi}"
  IO.println s!"term.lo={term12.re.lo}"
  IO.println s!"term.hi={term12.re.hi}"
  IO.println s!"sum.lo={state12.2.re.lo}"
  IO.println s!"sum.hi={state12.2.re.hi}"
