import SigmaC5M2TaylorStateStage7Certificate

open CarrySigmaObstruction ZetaLean ZetaLean.ComplexInterval

#eval do
  let state7 := c5M2Stage7
  let state8 := c5RoundedExpStateC 896 c5M2TaylorArgExport 8
  let term8 := (ComplexInterval.smulQ (1 / (Nat.factorial 7 : ℚ)) state7.1).coarsen 896
  IO.println s!"power.lo={state8.1.re.lo}"
  IO.println s!"power.hi={state8.1.re.hi}"
  IO.println s!"term.lo={term8.re.lo}"
  IO.println s!"term.hi={term8.re.hi}"
  IO.println s!"sum.lo={state8.2.re.lo}"
  IO.println s!"sum.hi={state8.2.re.hi}"
