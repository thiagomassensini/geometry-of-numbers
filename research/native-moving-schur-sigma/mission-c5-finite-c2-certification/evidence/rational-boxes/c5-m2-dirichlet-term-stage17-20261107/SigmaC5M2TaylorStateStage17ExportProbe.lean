import SigmaC5M2TaylorStateStage16Certificate

open CarrySigmaObstruction ZetaLean ZetaLean.ComplexInterval

#eval do
  let state16 := c5M2Stage16
  let state17 := c5RoundedExpStateC 896 c5M2TaylorArgExport 17
  let term17 := (ComplexInterval.smulQ (1 / (Nat.factorial 16 : ℚ)) state16.1).coarsen 896
  IO.println s!"power.lo={state17.1.re.lo}"
  IO.println s!"power.hi={state17.1.re.hi}"
  IO.println s!"term.lo={term17.re.lo}"
  IO.println s!"term.hi={term17.re.hi}"
  IO.println s!"sum.lo={state17.2.re.lo}"
  IO.println s!"sum.hi={state17.2.re.hi}"
