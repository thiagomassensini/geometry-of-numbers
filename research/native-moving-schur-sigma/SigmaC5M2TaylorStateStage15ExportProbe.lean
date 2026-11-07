import SigmaC5M2TaylorStateStage14Certificate

open CarrySigmaObstruction ZetaLean ZetaLean.ComplexInterval

#eval do
  let state14 := c5M2Stage14
  let state15 := c5RoundedExpStateC 896 c5M2TaylorArgExport 15
  let term15 := (ComplexInterval.smulQ (1 / (Nat.factorial 14 : ℚ)) state14.1).coarsen 896
  IO.println s!"power.lo={state15.1.re.lo}"
  IO.println s!"power.hi={state15.1.re.hi}"
  IO.println s!"term.lo={term15.re.lo}"
  IO.println s!"term.hi={term15.re.hi}"
  IO.println s!"sum.lo={state15.2.re.lo}"
  IO.println s!"sum.hi={state15.2.re.hi}"
