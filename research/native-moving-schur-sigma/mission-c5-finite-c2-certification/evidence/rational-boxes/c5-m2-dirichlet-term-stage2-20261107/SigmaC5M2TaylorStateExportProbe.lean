import SigmaC5Log2Certified

open CarrySigmaObstruction ZetaLean ZetaLean.ComplexInterval

def c5M2ExpArgExport : ComplexInterval :=
  (ComplexInterval.exact (2 / 5) 0).neg.mul
    { re := c5ExportedLogTwo512.coarsen 896,
      im := Interval.exact 0 }

def c5M2TaylorArgExport : ComplexInterval :=
  ComplexInterval.halveC
    (ComplexInterval.halveC
      (ComplexInterval.halveC
        (ComplexInterval.halveC c5M2ExpArgExport)))

#eval do
  let logTwo := c5ExportedLogTwo512.coarsen 896
  IO.println s!"log.lo={logTwo.lo}"
  IO.println s!"log.hi={logTwo.hi}"
  IO.println s!"arg.lo={c5M2ExpArgExport.re.lo}"
  IO.println s!"arg.hi={c5M2ExpArgExport.re.hi}"
  IO.println s!"taylor.lo={c5M2TaylorArgExport.re.lo}"
  IO.println s!"taylor.hi={c5M2TaylorArgExport.re.hi}"
  for n in List.range 193 do
    let st := c5RoundedExpStateC 896 c5M2TaylorArgExport n
    IO.println s!"{n}|{st.1.re.lo}|{st.1.re.hi}|{st.1.im.lo}|{st.1.im.hi}|{st.2.re.lo}|{st.2.re.hi}|{st.2.im.lo}|{st.2.im.hi}"
