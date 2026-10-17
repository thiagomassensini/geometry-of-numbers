import ExponentialEnclosures
import CoefficientData

/-! Executable integer enclosures of the fixed physical source. Soundness is
proved in SourceBoxes and FullSourceBoxes; this file contains no real oracle. -/
namespace CarryIntegralCertificate
set_option autoImplicit false
def Box.ofRat (q : ℚ) : Box := Box.rat q.num q.den

def piBox : Box :=
  (Box.rat 314159265358979323846 (10^20)).outer
    (Box.rat 314159265358979323847 (10^20))

def argumentBox (m : ℕ) (a : Box) : Box :=
  (piBox.mul ((Box.point ((m+1:ℕ):ℤ)).pow 2)).mul ((a.mul (.point 2)).exp)

def modeBox (m : ℕ) (a : Box) : Box :=
  ((Box.point 2).mul ((a.div (.point 2)).exp)).div ((argumentBox m a).exp)

def polynomialBox (n : ℕ) (x : Box) : Box :=
  Box.sum (fun r => (Box.ofRat ((thetaCoefficientCode n)[r]?.getD 0)).mul (x.pow r)) (n+1)

def derivativeBox (m n : ℕ) (a : Box) : Box :=
  (polynomialBox n (argumentBox m a)).mul (modeBox m a)

def majorantBox (m n : ℕ) (b : Box) : Box :=
  let q := argumentBox m b
  Box.sum (fun r => (Box.ofRat |(thetaCoefficientCode n)[r]?.getD 0|).mul
    (q.pow r)) (n+1)

def powerMassBox (p r : ℕ) (a b : Box) : Box :=
  Box.sum (fun k => ((((Box.point (Nat.fast_choose p k)).mul (a.pow (p-k))).mul
    ((b.add a.neg).pow (k+r+1))).div (.point ((k+r+1:ℕ):ℤ)))) (p+1)

def taylorMassBox (m n p : ℕ) (a b : Box) : Box :=
  let q := argumentBox m a
  let f := modeBox m a
  Box.sum (fun r => (((polynomialBox r q).mul f).div (.point (r.factorial:ℤ))).mul
    (powerMassBox p r a b)) (n+1)

def cellBox (m n p : ℕ) (a b : Box) : Box :=
  let v := taylorMassBox m n p a b
  let e := (((majorantBox m (n+1) b).mul (modeBox m a)).div (.point (n.factorial:ℤ))).mul
    (powerMassBox p (n+1) a b)
  (v.add e.neg).outer (v.add e)

def gridBox (j grid : ℕ) : Box := Box.rat j grid

def finiteModeBox (m n p grid count : ℕ) : Box :=
  Box.sum (fun j => cellBox m n p (gridBox j grid) (gridBox (j+1) grid)) count

def decayBox (m p : ℕ) (L : Box) : Box :=
  (((Box.point 2).mul (argumentBox m L)).add (Box.rat 1 2).neg).add
    ((Box.point p).div L).neg

def tailModeBox (m p : ℕ) (L : Box) : Box :=
  (Box.point 0).outer (((modeBox m L).mul (L.pow p)).div (decayBox m p L))

def fullModeBox (m n p grid count : ℕ) : Box :=
  (finiteModeBox m n p grid count).add (tailModeBox m p (gridBox count grid))

def fullThetaMomentBox (p : ℕ) : Box :=
  (((fullModeBox 0 15 p 64 96).add (fullModeBox 1 15 p 64 64)).add
    (fullModeBox 2 15 p 64 48)).add
      ((Box.point 0).outer (Box.rat p.factorial ((10:ℤ)^20*95^(p+1))))

end CarryIntegralCertificate
