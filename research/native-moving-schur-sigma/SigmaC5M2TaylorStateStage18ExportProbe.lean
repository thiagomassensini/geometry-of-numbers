import SigmaC5M2TaylorStateStage17Certificate

open CarrySigmaObstruction ZetaLean ZetaLean.ComplexInterval

#eval do
  let state17 := c5M2Stage17
  let state18 := c5RoundedExpStateC 896 c5M2TaylorArgExport 18
  let term18 := (ComplexInterval.smulQ (1 / (Nat.factorial 17 : ℚ)) state17.1).coarsen 896
  IO.println s!"power.lo={state18.1.re.lo}"
  IO.println s!"power.hi={state18.1.re.hi}"
  IO.println s!"term.lo={term18.re.lo}"
  IO.println s!"term.hi={term18.re.hi}"
  IO.println s!"sum.lo={state18.2.re.lo}"
  IO.println s!"sum.hi={state18.2.re.hi}"
