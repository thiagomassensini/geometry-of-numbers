import SigmaC5RationalNodeCenteredInstantiate

open CarrySigmaObstruction
open ZetaLean

def c5CenteredSharedTableProbeBoxes : List ComplexInterval :=
  let bernTable := c5BernoulliPrimeTable 601
  (List.range 3).map fun j =>
    c5RationalZetaCenteredNodeBoxWithTable 512 192 896 (3 / 5)
      ((j : ℚ) / 100000) bernTable

#eval c5CenteredSharedTableProbeBoxes.map fun (box : ComplexInterval) =>
  let reWidth : ℚ := box.re.hi - box.re.lo
  let imWidth : ℚ := box.im.hi - box.im.lo
  ((reWidth.num.natAbs.log2, reWidth.den.log2),
    (imWidth.num.natAbs.log2, imWidth.den.log2))
