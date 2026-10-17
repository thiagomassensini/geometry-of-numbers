import NodeCacheData

/-! The same enclosure program with source-node witnesses factored out.
NodeCacheEquivalence proves literal equality to the original program. -/
namespace CarryIntegralCertificate
set_option autoImplicit false

def cachedMajorantBox (m n j : ℕ) : Box :=
  let q := cachedArgumentNode m j
  Box.sum (fun r => (Box.ofRat |(thetaCoefficientCode n)[r]?.getD 0|).mul
    (q.pow r)) (n+1)

def cachedTaylorMassBox (m n p j : ℕ) : Box :=
  let q := cachedArgumentNode m j
  let f := cachedModeNode m j
  Box.sum (fun r => (((polynomialBox r q).mul f).div (.point (r.factorial:ℤ))).mul
    (powerMassBox p r (gridBox j 64) (gridBox (j+1) 64))) (n+1)

def cachedCellBox (m n p j : ℕ) : Box :=
  let v := cachedTaylorMassBox m n p j
  let e := (((cachedMajorantBox m (n+1) (j+1)).mul (cachedModeNode m j)).div
    (.point (n.factorial:ℤ))).mul
      (powerMassBox p (n+1) (gridBox j 64) (gridBox (j+1) 64))
  (v.add e.neg).outer (v.add e)

def cachedFiniteModeBox (m n p : ℕ) : Box :=
  Box.sum (cachedCellBox m n p) (thetaCertificateCellCount m)

def cachedDecayBox (m p j : ℕ) : Box :=
  (((Box.point 2).mul (cachedArgumentNode m j)).add (Box.rat 1 2).neg).add
    ((Box.point p).div (gridBox j 64)).neg

def cachedTailModeBox (m p j : ℕ) : Box :=
  (Box.point 0).outer (((cachedModeNode m j).mul ((gridBox j 64).pow p)).div
    (cachedDecayBox m p j))

def cachedFullModeBox (m n p : ℕ) : Box :=
  (cachedFiniteModeBox m n p).add (cachedTailModeBox m p (thetaCertificateCellCount m))

def cachedFullThetaMomentBox (p : ℕ) : Box :=
  (((cachedFullModeBox 0 15 p).add (cachedFullModeBox 1 15 p)).add
    (cachedFullModeBox 2 15 p)).add
      ((Box.point 0).outer (Box.rat p.factorial ((10:ℤ)^20*95^(p+1))))

end CarryIntegralCertificate
