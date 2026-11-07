import SigmaC5FastBernoulliTable

open CarrySigmaObstruction

#eval let c := (c5BernoulliPrimeTable 601).getD 600 0
  (c.num.natAbs.log2, c.den.log2)
