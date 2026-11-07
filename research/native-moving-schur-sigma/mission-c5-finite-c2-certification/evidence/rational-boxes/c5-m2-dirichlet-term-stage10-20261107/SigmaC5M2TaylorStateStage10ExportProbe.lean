import SigmaC5M2TaylorStateStage9Certificate

open CarrySigmaObstruction ZetaLean ZetaLean.ComplexInterval

#eval do
  let state9 := c5M2Stage9
  let state10 := c5RoundedExpStateC 896 c5M2TaylorArgExport 10
  let term10 := (ComplexInterval.smulQ (1 / (Nat.factorial 9 : ℚ)) state9.1).coarsen 896
  IO.println s!"power.lo={state10.1.re.lo}"
  IO.println s!"power.hi={state10.1.re.hi}"
  IO.println s!"term.lo={term10.re.lo}"
  IO.println s!"term.hi={term10.re.hi}"
  IO.println s!"sum.lo={state10.2.re.lo}"
  IO.println s!"sum.hi={state10.2.re.hi}"
