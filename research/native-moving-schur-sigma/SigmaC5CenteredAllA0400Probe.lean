import SigmaC5RationalNodeCenteredInstantiate

open CarrySigmaObstruction ZetaLean

#eval do
  let bernTable := c5BernoulliPrimeTable 601
  (List.range 129).forM fun j => do
    let a : ℚ := 2 / 5
    let b : ℚ := (j : ℚ) / 100000
    let box := c5RationalZetaCenteredNodeBoxWithTable 512 192 896 a b bernTable
    IO.println s!"{j}, {box.re.lo}, {box.re.hi}, {box.im.lo}, {box.im.hi}"
