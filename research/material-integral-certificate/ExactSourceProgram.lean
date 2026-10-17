import ExactGridWeights
import CachedSourceProgram

/-! Source quadrature with the same exact grid weights, rounded only once. -/
namespace CarryIntegralCertificate
set_option autoImplicit false

def exactTaylorMassBox (m n p j : ℕ) : Box :=
  let q := cachedArgumentNode m j
  let f := cachedModeNode m j
  Box.sum (fun r => (((polynomialBox r q).mul f).div (.point (r.factorial:ℤ))).mulNonnegRat
    (rationalGridWeight p r j)) (n+1)

def exactCellBox (m n p j : ℕ) : Box :=
  let v := exactTaylorMassBox m n p j
  let e := (((cachedMajorantBox m (n+1) (j+1)).mul (cachedModeNode m j)).div
    (.point (n.factorial:ℤ))).mulNonnegRat (rationalGridWeight p (n+1) j)
  (v.add e.neg).outer (v.add e)

def exactFiniteModeBox (m n p : ℕ) : Box :=
  Box.sum (exactCellBox m n p) (thetaCertificateCellCount m)

def exactFullModeBox (m n p : ℕ) : Box :=
  (exactFiniteModeBox m n p).add (cachedTailModeBox m p (thetaCertificateCellCount m))

def exactFullThetaMomentBox (p : ℕ) : Box :=
  (((exactFullModeBox 0 15 p).add (exactFullModeBox 1 15 p)).add
    (exactFullModeBox 2 15 p)).add
      ((Box.point 0).outer (Box.rat p.factorial ((10:ℤ)^20*95^(p+1))))

end CarryIntegralCertificate
