import SigmaC5M2TaylorStateStage12Certificate

open CarrySigmaObstruction ZetaLean ZetaLean.ComplexInterval

#eval do
  let state12 := c5M2Stage12
  let state13 := c5RoundedExpStateC 896 c5M2TaylorArgExport 13
  let term13 := (ComplexInterval.smulQ (1 / (Nat.factorial 12 : ℚ)) state12.1).coarsen 896
  IO.println s!"power.lo={state13.1.re.lo}"
  IO.println s!"power.hi={state13.1.re.hi}"
  IO.println s!"term.lo={term13.re.lo}"
  IO.println s!"term.hi={term13.re.hi}"
  IO.println s!"sum.lo={state13.2.re.lo}"
  IO.println s!"sum.hi={state13.2.re.hi}"
