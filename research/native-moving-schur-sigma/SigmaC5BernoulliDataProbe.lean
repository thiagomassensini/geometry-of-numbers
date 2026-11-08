import SigmaC5FastBernoulliTable

open CarrySigmaObstruction

#eval do
  let table := c5BernoulliPrimeTable 601
  for i in [0:601] do
    IO.println s!"{i}: {table.getD i 0}"
