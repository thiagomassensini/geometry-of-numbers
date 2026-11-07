import SigmaC5M2TaylorStateStage8Certificate

open CarrySigmaObstruction ZetaLean ZetaLean.ComplexInterval

#eval do
  let state8 := c5M2Stage8
  let state9 := c5RoundedExpStateC 896 c5M2TaylorArgExport 9
  let term9 := (ComplexInterval.smulQ (1 / (Nat.factorial 8 : ℚ)) state8.1).coarsen 896
  IO.println s!"power.lo={state9.1.re.lo}"
  IO.println s!"power.hi={state9.1.re.hi}"
  IO.println s!"term.lo={term9.re.lo}"
  IO.println s!"term.hi={term9.re.hi}"
  IO.println s!"sum.lo={state9.2.re.lo}"
  IO.println s!"sum.hi={state9.2.re.hi}"
