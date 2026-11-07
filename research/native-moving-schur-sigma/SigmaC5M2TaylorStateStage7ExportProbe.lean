import SigmaC5M2TaylorStateStage6Certificate

open CarrySigmaObstruction ZetaLean ZetaLean.ComplexInterval

#eval do
  let state6 := c5M2Stage6
  let state7 := c5RoundedExpStateC 896 c5M2TaylorArgExport 7
  let term7 := (ComplexInterval.smulQ (1 / (Nat.factorial 6 : ℚ)) state6.1).coarsen 896
  IO.println s!"power.lo={state7.1.re.lo}"
  IO.println s!"power.hi={state7.1.re.hi}"
  IO.println s!"term.lo={term7.re.lo}"
  IO.println s!"term.hi={term7.re.hi}"
  IO.println s!"sum.lo={state7.2.re.lo}"
  IO.println s!"sum.hi={state7.2.re.hi}"
