import SigmaC5RationalNodeCenteredInstantiate

open CarrySigmaObstruction ZetaLean

def c5Centered129SharedTableProbeBoxes : List ComplexInterval :=
  let bernTable := c5BernoulliPrimeTable 601
  (List.range 129).map fun j =>
    c5RationalZetaCenteredNodeBoxWithTable 512 192 896 (3 / 5)
      ((j : ℚ) / 100000) bernTable

#eval (c5Centered129SharedTableProbeBoxes.map fun (box : ComplexInterval) =>
  (box.re.hi - box.re.lo).den.log2 +
    (box.im.hi - box.im.lo).den.log2).sum
