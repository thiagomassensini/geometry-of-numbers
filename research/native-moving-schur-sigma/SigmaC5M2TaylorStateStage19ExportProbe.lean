import SigmaC5M2TaylorStateStage18Certificate

open CarrySigmaObstruction ZetaLean ZetaLean.ComplexInterval

#eval do
  let state18 := c5M2Stage18
  let state19 := c5RoundedExpStateC 896 c5M2TaylorArgExport 19
  let term19 := (ComplexInterval.smulQ (1 / (Nat.factorial 18 : ℚ)) state18.1).coarsen 896
  IO.println s!"power.lo={state19.1.re.lo}"
  IO.println s!"power.hi={state19.1.re.hi}"
  IO.println s!"term.lo={term19.re.lo}"
  IO.println s!"term.hi={term19.re.hi}"
  IO.println s!"sum.lo={state19.2.re.lo}"
  IO.println s!"sum.hi={state19.2.re.hi}"
