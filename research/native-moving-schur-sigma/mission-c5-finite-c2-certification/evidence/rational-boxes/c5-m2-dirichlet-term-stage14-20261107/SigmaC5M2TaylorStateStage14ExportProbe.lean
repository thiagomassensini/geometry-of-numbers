import SigmaC5M2TaylorStateStage13Certificate

open CarrySigmaObstruction ZetaLean ZetaLean.ComplexInterval

#eval do
  let state13 := c5M2Stage13
  let state14 := c5RoundedExpStateC 896 c5M2TaylorArgExport 14
  let term14 := (ComplexInterval.smulQ (1 / (Nat.factorial 13 : ℚ)) state13.1).coarsen 896
  IO.println s!"power.lo={state14.1.re.lo}"
  IO.println s!"power.hi={state14.1.re.hi}"
  IO.println s!"term.lo={term14.re.lo}"
  IO.println s!"term.hi={term14.re.hi}"
  IO.println s!"sum.lo={state14.2.re.lo}"
  IO.println s!"sum.hi={state14.2.re.hi}"
