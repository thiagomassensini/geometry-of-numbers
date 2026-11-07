import SigmaC5RationalNodeCenteredInstantiate

open CarrySigmaObstruction ZetaLean

#eval do
  let bernTable := c5BernoulliPrimeTable 601
  (List.range 129).forM fun j => do
    let b : ℚ := (j : ℚ) / 100000
    let box := c5RationalZetaCenteredNodeBoxWithTable 512 192 896
      (3 / 5) b bernTable
    let reWidth : ℚ := box.re.hi - box.re.lo
    let imWidth : ℚ := box.im.hi - box.im.lo
    IO.println s!"{j}: ({reWidth.num.natAbs.log2}, {reWidth.den.log2}), ({imWidth.num.natAbs.log2}, {imWidth.den.log2})"
