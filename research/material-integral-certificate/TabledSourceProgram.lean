import ExactSourceProgram
import QuadratureCacheData
namespace CarryIntegralCertificate
set_option autoImplicit false

def tabledTaylorMassBox (m p j : ℕ) : Box :=
  Box.sum (fun r => (cachedQuadratureCoefficient m j r).mulNonnegRat (rationalGridWeight p r j)) 16

def tabledCellBox (m p j : ℕ) : Box :=
  let v := tabledTaylorMassBox m p j
  let e := (cachedQuadratureError m j).mulNonnegRat (rationalGridWeight p 16 j)
  (v.add e.neg).outer (v.add e)

def tabledFiniteModeBox (m p : ℕ) : Box :=
  Box.sum (tabledCellBox m p) (thetaCertificateCellCount m)

def tabledFullModeBox (m p : ℕ) : Box :=
  (tabledFiniteModeBox m p).add (cachedTailModeBox m p (thetaCertificateCellCount m))

def tabledFullThetaMomentBox (p : ℕ) : Box :=
  (((tabledFullModeBox 0 p).add (tabledFullModeBox 1 p)).add (tabledFullModeBox 2 p)).add
    ((Box.point 0).outer (Box.rat p.factorial ((10:ℤ)^20*95^(p+1))))

end CarryIntegralCertificate
