import SigmaC5RationalNodeCenteredInstantiate

open CarrySigmaObstruction ZetaLean

#eval do
  let x := c5CenteredLog2I 512
  IO.println s!"{x.lo}, {x.hi}"
