import SigmaC5M2TaylorStateStage10Certificate

open CarrySigmaObstruction ZetaLean ZetaLean.ComplexInterval

#eval do
  let state10 := c5M2Stage10
  let state11 := c5RoundedExpStateC 896 c5M2TaylorArgExport 11
  let term11 := (ComplexInterval.smulQ (1 / (Nat.factorial 10 : ℚ)) state10.1).coarsen 896
  IO.println s!"power.lo={state11.1.re.lo}"
  IO.println s!"power.hi={state11.1.re.hi}"
  IO.println s!"term.lo={term11.re.lo}"
  IO.println s!"term.hi={term11.re.hi}"
  IO.println s!"sum.lo={state11.2.re.lo}"
  IO.println s!"sum.hi={state11.2.re.hi}"
