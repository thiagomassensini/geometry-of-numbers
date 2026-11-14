import FourthSourceGate17
import NativeEvenCertificate
import Mathlib.LinearAlgebra.Matrix.Adjugate

namespace C3ShiftedFourth

open C3Cofactor C3GeneralCofactor CarrySourceBezout CarrySelfAdjointOperator
  C3CofactorCorrelation
open scoped BigOperators Matrix

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 50000

private def cb17 (j : Fin 9) : RationalBall := normalizedCoefficientCandidate17 j

def evenAReal17 (c : Fin 9 → ℝ) := -(c 0 * c 1)
def evenBReal17 (c : Fin 9 → ℝ) := -2 * (c 0 * c 2)
def evenEReal17 (c : Fin 9 → ℝ) := -3 * (c 0 * c 3)
def evenDReal17 (c : Fin 9 → ℝ) := -3 * (c 0 * c 3) - c 1 * c 2
def evenFReal17 (c : Fin 9 → ℝ) := -4 * (c 0 * c 4) - 2 * (c 1 * c 3)
def evenGReal17 (c : Fin 9 → ℝ) :=
  -5 * (c 0 * c 5) - 3 * (c 1 * c 4) - c 2 * c 3
def evenHReal17 (c : Fin 9 → ℝ) := -4 * (c 0 * c 4)
def evenIReal17 (c : Fin 9 → ℝ) := -5 * (c 0 * c 5) - 3 * (c 1 * c 4)
def evenJReal17 (c : Fin 9 → ℝ) :=
  -6 * (c 0 * c 6) - 4 * (c 1 * c 5) - 2 * (c 2 * c 4)
def evenKReal17 (c : Fin 9 → ℝ) :=
  -7 * (c 0 * c 7) - 5 * (c 1 * c 6) - 3 * (c 2 * c 5) - c 3 * c 4

private def rbAdd17 (a b : RationalBall) := a.add b
private def rbSub17 (a b : RationalBall) := a.sub b
private def rbMul17 (a b : RationalBall) := a.mul b
private def rbScale17 (q : ℚ) (a : RationalBall) := RationalBall.point q |>.mul a
private def rbNeg17 (a : RationalBall) := a.neg

private def evenABall17 := rbNeg17 (rbMul17 (cb17 0) (cb17 1))
private def evenBBall17 := rbScale17 (-2) (rbMul17 (cb17 0) (cb17 2))
private def evenEBall17 := rbScale17 (-3) (rbMul17 (cb17 0) (cb17 3))
private def evenDBall17 := rbSub17 evenEBall17 (rbMul17 (cb17 1) (cb17 2))
private def evenFBall17 := rbSub17
  (rbScale17 (-4) (rbMul17 (cb17 0) (cb17 4)))
  (rbScale17 2 (rbMul17 (cb17 1) (cb17 3)))
private def evenGBall17 := rbSub17
  (rbSub17 (rbScale17 (-5) (rbMul17 (cb17 0) (cb17 5)))
    (rbScale17 3 (rbMul17 (cb17 1) (cb17 4))))
  (rbMul17 (cb17 2) (cb17 3))
private def evenHBall17 := rbScale17 (-4) (rbMul17 (cb17 0) (cb17 4))
private def evenIBall17 := rbSub17
  (rbScale17 (-5) (rbMul17 (cb17 0) (cb17 5)))
  (rbScale17 3 (rbMul17 (cb17 1) (cb17 4)))
private def evenJBall17 := rbSub17
  (rbSub17 (rbScale17 (-6) (rbMul17 (cb17 0) (cb17 6)))
    (rbScale17 4 (rbMul17 (cb17 1) (cb17 5))))
  (rbScale17 2 (rbMul17 (cb17 2) (cb17 4)))
private def evenKBall17 := rbSub17
  (rbSub17 (rbSub17 (rbScale17 (-7) (rbMul17 (cb17 0) (cb17 7)))
    (rbScale17 5 (rbMul17 (cb17 1) (cb17 6))))
    (rbScale17 3 (rbMul17 (cb17 2) (cb17 5))))
  (rbMul17 (cb17 3) (cb17 4))

private theorem even_component_balls17_contains (c : Fin 9 → ℝ)
    (hc : ∀ j, (cb17 j).Contains (c j)) :
    evenABall17.Contains (evenAReal17 c) ∧
    evenBBall17.Contains (evenBReal17 c) ∧
    evenEBall17.Contains (evenEReal17 c) ∧
    evenDBall17.Contains (evenDReal17 c) ∧
    evenFBall17.Contains (evenFReal17 c) ∧
    evenGBall17.Contains (evenGReal17 c) ∧
    evenHBall17.Contains (evenHReal17 c) ∧
    evenIBall17.Contains (evenIReal17 c) ∧
    evenJBall17.Contains (evenJReal17 c) ∧
    evenKBall17.Contains (evenKReal17 c) := by
  have h0 := hc 0
  have h1 := hc 1
  have h2 := hc 2
  have h3 := hc 3
  have h4 := hc 4
  have h5 := hc 5
  have h6 := hc 6
  have h7 := hc 7
  have h8 := hc 8
  dsimp [cb17] at h0 h1 h2 h3 h4 h5 h6 h7 h8
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [evenABall17, evenBBall17, evenEBall17, evenDBall17, evenFBall17,
      evenGBall17, evenHBall17, evenIBall17, evenJBall17, evenKBall17,
      evenAReal17, evenBReal17, evenEReal17, evenDReal17, evenFReal17,
      evenGReal17, evenHReal17, evenIReal17, evenJReal17, evenKReal17,
      cb17, rbSub17, rbMul17, rbScale17, rbNeg17,
      RationalBall.sub, sub_eq_add_neg] <;>
    repeat first
      | assumption
      | apply RationalBall.add_contains
      | apply RationalBall.neg_contains
      | apply RationalBall.mul_contains
      | norm_num [RationalBall.point, RationalBall.Contains]

private def evenU0Q17 : ℚ := 15742061093751 / 20000000000000000000
private def evenU1Q17 : ℚ := 33937512074551473 / 250000000000000000000
private def evenU2Q17 : ℚ := 16197205068313371127 / 1000000000000000000000
private def evenU0Real17 : ℝ := evenU0Q17
private def evenU1Real17 : ℝ := evenU1Q17
private def evenU2Real17 : ℝ := evenU2Q17
private def evenU0Ball17 := RationalBall.point evenU0Q17
private def evenU1Ball17 := RationalBall.point evenU1Q17
private def evenU2Ball17 := RationalBall.point evenU2Q17

private def evenDetAReal17 (a b e d f g : ℝ) :=
  (a*d)*g + 2*((b*e)*f) - a*(f*f) - d*(e*e) - g*(b*b)
private def evenEnergyReal17 (a b e d f g h i j k : ℝ) :=
  a*(evenU0Real17*evenU0Real17) + (2*b)*(evenU0Real17*evenU1Real17) +
    (2*e)*(evenU0Real17*evenU2Real17) + d*(evenU1Real17*evenU1Real17) +
    (2*f)*(evenU1Real17*evenU2Real17) + g*(evenU2Real17*evenU2Real17) +
    (2*h)*evenU0Real17 + (2*i)*evenU1Real17 + (2*j)*evenU2Real17 + k
private def evenR0Real17 (a b e h : ℝ) :=
  a*evenU0Real17 + b*evenU1Real17 + e*evenU2Real17 + h
private def evenR1Real17 (b d f i : ℝ) :=
  b*evenU0Real17 + d*evenU1Real17 + f*evenU2Real17 + i
private def evenR2Real17 (e f g j : ℝ) :=
  e*evenU0Real17 + f*evenU1Real17 + g*evenU2Real17 + j
private def evenAdjQuadReal17 (a b e d f g r0 r1 r2 : ℝ) :=
  (d*g-f*f)*(r0*r0) + (a*g-e*e)*(r1*r1) + (a*d-b*b)*(r2*r2) +
    (2*(e*f-b*g))*(r0*r1) + (2*(b*f-d*e))*(r0*r2) +
      (2*(b*e-a*f))*(r1*r2)
private def evenGateReal17 (a b e d f g h i j k : ℝ) :=
  evenDetAReal17 a b e d f g * evenEnergyReal17 a b e d f g h i j k -
    evenAdjQuadReal17 a b e d f g (evenR0Real17 a b e h)
      (evenR1Real17 b d f i) (evenR2Real17 e f g j)

private def evenDetABall17 :=
  rbSub17 (rbSub17 (rbSub17
    (rbAdd17 (rbMul17 (rbMul17 evenABall17 evenDBall17) evenGBall17)
      (rbScale17 2 (rbMul17 (rbMul17 evenBBall17 evenEBall17) evenFBall17)))
    (rbMul17 evenABall17 (rbMul17 evenFBall17 evenFBall17)))
    (rbMul17 evenDBall17 (rbMul17 evenEBall17 evenEBall17)))
    (rbMul17 evenGBall17 (rbMul17 evenBBall17 evenBBall17))
private def evenEnergyBall17 :=
  rbAdd17 (rbAdd17 (rbAdd17 (rbAdd17 (rbAdd17 (rbAdd17 (rbAdd17 (rbAdd17 (rbAdd17
    (rbMul17 evenABall17 (rbMul17 evenU0Ball17 evenU0Ball17))
    (rbMul17 (rbScale17 2 evenBBall17) (rbMul17 evenU0Ball17 evenU1Ball17)))
    (rbMul17 (rbScale17 2 evenEBall17) (rbMul17 evenU0Ball17 evenU2Ball17)))
    (rbMul17 evenDBall17 (rbMul17 evenU1Ball17 evenU1Ball17)))
    (rbMul17 (rbScale17 2 evenFBall17) (rbMul17 evenU1Ball17 evenU2Ball17)))
    (rbMul17 evenGBall17 (rbMul17 evenU2Ball17 evenU2Ball17)))
    (rbMul17 (rbScale17 2 evenHBall17) evenU0Ball17))
    (rbMul17 (rbScale17 2 evenIBall17) evenU1Ball17))
    (rbMul17 (rbScale17 2 evenJBall17) evenU2Ball17))
    evenKBall17
private def evenR0Ball17 := rbAdd17 (rbAdd17 (rbAdd17
  (rbMul17 evenABall17 evenU0Ball17) (rbMul17 evenBBall17 evenU1Ball17))
  (rbMul17 evenEBall17 evenU2Ball17)) evenHBall17
private def evenR1Ball17 := rbAdd17 (rbAdd17 (rbAdd17
  (rbMul17 evenBBall17 evenU0Ball17) (rbMul17 evenDBall17 evenU1Ball17))
  (rbMul17 evenFBall17 evenU2Ball17)) evenIBall17
private def evenR2Ball17 := rbAdd17 (rbAdd17 (rbAdd17
  (rbMul17 evenEBall17 evenU0Ball17) (rbMul17 evenFBall17 evenU1Ball17))
  (rbMul17 evenGBall17 evenU2Ball17)) evenJBall17
private def evenAdjQuadBall17 :=
  rbAdd17 (rbAdd17 (rbAdd17 (rbAdd17 (rbAdd17
    (rbMul17 (rbSub17 (rbMul17 evenDBall17 evenGBall17)
      (rbMul17 evenFBall17 evenFBall17)) (rbMul17 evenR0Ball17 evenR0Ball17))
    (rbMul17 (rbSub17 (rbMul17 evenABall17 evenGBall17)
      (rbMul17 evenEBall17 evenEBall17)) (rbMul17 evenR1Ball17 evenR1Ball17)))
    (rbMul17 (rbSub17 (rbMul17 evenABall17 evenDBall17)
      (rbMul17 evenBBall17 evenBBall17)) (rbMul17 evenR2Ball17 evenR2Ball17)))
    (rbMul17 (rbScale17 2 (rbSub17 (rbMul17 evenEBall17 evenFBall17)
      (rbMul17 evenBBall17 evenGBall17))) (rbMul17 evenR0Ball17 evenR1Ball17)))
    (rbMul17 (rbScale17 2 (rbSub17 (rbMul17 evenBBall17 evenFBall17)
      (rbMul17 evenDBall17 evenEBall17))) (rbMul17 evenR0Ball17 evenR2Ball17)))
    (rbMul17 (rbScale17 2 (rbSub17 (rbMul17 evenBBall17 evenEBall17)
      (rbMul17 evenABall17 evenFBall17))) (rbMul17 evenR1Ball17 evenR2Ball17))
private def evenGateBall17 :=
  rbSub17 (rbMul17 evenDetABall17 evenEnergyBall17) evenAdjQuadBall17

private def roundedEvenBall30 (centerUnits radiusUnits : Int) : RationalBall :=
  ⟨(centerUnits : ℚ) / 10^30, (radiusUnits : ℚ) / 10^30⟩

private def roundedEvenBall35 (centerUnits radiusUnits : Int) : RationalBall :=
  ⟨(centerUnits : ℚ) / 10^35, (radiusUnits : ℚ) / 10^35⟩

private def roundedEvenBall50 (centerUnits radiusUnits : Int) : RationalBall :=
  ⟨(centerUnits : ℚ) / 10^50, (radiusUnits : ℚ) / 10^50⟩

private def evenACoarse17 := roundedEvenBall30
  23104993115418970788933810430 1000000001
private def evenBCoarse17 := roundedEvenBall30
  (-496668107578288351447712890) 2000000002
private def evenECoarse17 := roundedEvenBall30
  5023057883954849582965887 300000003
private def evenDCoarse17 := roundedEvenBall30
  10760814487077110139243109 323353331
private def evenFCoarse17 := roundedEvenBall30
  (-109494601568926702251513) 44624352
private def evenGCoarse17 := roundedEvenBall30
  1119453189357186305628 5719687
private def evenHCoarse17 := roundedEvenBall30
  (-32122789684174846844988) 40000004
private def evenICoarse17 := roundedEvenBall30
  703654413777176859165 5693180
private def evenJCoarse17 := roundedEvenBall30
  (-7221779625354418487) 6097410
private def evenKCoarse17 := roundedEvenBall30
  46735524976280439 816295

private def evenDetACalc17 :=
  rbSub17 (rbSub17 (rbSub17
    (rbAdd17 (rbMul17 (rbMul17 evenACoarse17 evenDCoarse17) evenGCoarse17)
      (rbScale17 2 (rbMul17 (rbMul17 evenBCoarse17 evenECoarse17) evenFCoarse17)))
    (rbMul17 evenACoarse17 (rbMul17 evenFCoarse17 evenFCoarse17)))
    (rbMul17 evenDCoarse17 (rbMul17 evenECoarse17 evenECoarse17)))
    (rbMul17 evenGCoarse17 (rbMul17 evenBCoarse17 evenBCoarse17))
private def evenDetACoarse17 := roundedEvenBall35
  21728105105262 336749

private def evenEnergyCalc17 :=
  rbAdd17 (rbAdd17 (rbAdd17 (rbAdd17 (rbAdd17 (rbAdd17 (rbAdd17 (rbAdd17 (rbAdd17
    (rbMul17 evenACoarse17 (rbMul17 evenU0Ball17 evenU0Ball17))
    (rbMul17 (rbScale17 2 evenBCoarse17) (rbMul17 evenU0Ball17 evenU1Ball17)))
    (rbMul17 (rbScale17 2 evenECoarse17) (rbMul17 evenU0Ball17 evenU2Ball17)))
    (rbMul17 evenDCoarse17 (rbMul17 evenU1Ball17 evenU1Ball17)))
    (rbMul17 (rbScale17 2 evenFCoarse17) (rbMul17 evenU1Ball17 evenU2Ball17)))
    (rbMul17 evenGCoarse17 (rbMul17 evenU2Ball17 evenU2Ball17)))
    (rbMul17 (rbScale17 2 evenHCoarse17) evenU0Ball17))
    (rbMul17 (rbScale17 2 evenICoarse17) evenU1Ball17))
    (rbMul17 (rbScale17 2 evenJCoarse17) evenU2Ball17))
    evenKCoarse17
private def evenEnergyCoarse17 := roundedEvenBall35
  5419624538519107 101713649785

private def evenR0Calc17 := rbAdd17 (rbAdd17 (rbAdd17
  (rbMul17 evenACoarse17 evenU0Ball17) (rbMul17 evenBCoarse17 evenU1Ball17))
  (rbMul17 evenECoarse17 evenU2Ball17)) evenHCoarse17
private def evenR1Calc17 := rbAdd17 (rbAdd17 (rbAdd17
  (rbMul17 evenBCoarse17 evenU0Ball17) (rbMul17 evenDCoarse17 evenU1Ball17))
  (rbMul17 evenFCoarse17 evenU2Ball17)) evenICoarse17
private def evenR2Calc17 := rbAdd17 (rbAdd17 (rbAdd17
  (rbMul17 evenECoarse17 evenU0Ball17) (rbMul17 evenFCoarse17 evenU1Ball17))
  (rbMul17 evenGCoarse17 evenU2Ball17)) evenJCoarse17
private def evenR0Coarse17 := roundedEvenBall35
  91229549079 4513145276902
private def evenR1Coarse17 := roundedEvenBall35
  (-1957148536) 646143921681
private def evenR2Coarse17 := roundedEvenBall35
  19611589 619634683213

private def evenAdjQuadCalc17 :=
  rbAdd17 (rbAdd17 (rbAdd17 (rbAdd17 (rbAdd17
    (rbMul17 (rbSub17 (rbMul17 evenDCoarse17 evenGCoarse17)
      (rbMul17 evenFCoarse17 evenFCoarse17)) (rbMul17 evenR0Coarse17 evenR0Coarse17))
    (rbMul17 (rbSub17 (rbMul17 evenACoarse17 evenGCoarse17)
      (rbMul17 evenECoarse17 evenECoarse17)) (rbMul17 evenR1Coarse17 evenR1Coarse17)))
    (rbMul17 (rbSub17 (rbMul17 evenACoarse17 evenDCoarse17)
      (rbMul17 evenBCoarse17 evenBCoarse17)) (rbMul17 evenR2Coarse17 evenR2Coarse17)))
    (rbMul17 (rbScale17 2 (rbSub17 (rbMul17 evenECoarse17 evenFCoarse17)
      (rbMul17 evenBCoarse17 evenGCoarse17))) (rbMul17 evenR0Coarse17 evenR1Coarse17)))
    (rbMul17 (rbScale17 2 (rbSub17 (rbMul17 evenBCoarse17 evenFCoarse17)
      (rbMul17 evenDCoarse17 evenECoarse17))) (rbMul17 evenR0Coarse17 evenR2Coarse17)))
    (rbMul17 (rbScale17 2 (rbSub17 (rbMul17 evenBCoarse17 evenECoarse17)
      (rbMul17 evenACoarse17 evenFCoarse17))) (rbMul17 evenR1Coarse17 evenR2Coarse17))
private def evenAdjQuadCoarse17 := roundedEvenBall50
  0 2
private def evenGateCalc17 :=
  rbSub17 (rbMul17 evenDetACoarse17 evenEnergyCoarse17) evenAdjQuadCoarse17
private def evenGateCoarse17 := roundedEvenBall50
  1177581716 22122

private theorem RationalBall.refine_contains17 {a b : RationalBall} {x : ℝ}
    (hbound : |a.center - b.center| + a.radius ≤ b.radius)
    (ha : a.Contains x) : b.Contains x := by
  change |x - (b.center : ℝ)| ≤ (b.radius : ℝ)
  have htri : |x - (b.center : ℝ)| ≤
      |x - (a.center : ℝ)| + |(a.center : ℝ) - (b.center : ℝ)| := by
    have heq : x - (b.center : ℝ) =
        (x - (a.center : ℝ)) + ((a.center : ℝ) - (b.center : ℝ)) := by ring
    rw [heq]
    exact abs_add_le _ _
  have hboundR : |(a.center : ℝ) - (b.center : ℝ)| + (a.radius : ℝ) ≤
      (b.radius : ℝ) := by exact_mod_cast hbound
  calc
    |x - (b.center : ℝ)| ≤ |x - (a.center : ℝ)| + |(a.center : ℝ) - (b.center : ℝ)| := htri
    _ ≤ (a.radius : ℝ) + |(a.center : ℝ) - (b.center : ℝ)| := add_le_add ha le_rfl
    _ = |(a.center : ℝ) - (b.center : ℝ)| + (a.radius : ℝ) := add_comm _ _
    _ ≤ (b.radius : ℝ) := hboundR

private theorem evenABall17_refines :
    |evenABall17.center - evenACoarse17.center| + evenABall17.radius ≤
      evenACoarse17.radius := by
  norm_num [evenABall17, evenACoarse17, roundedEvenBall30, cb17,
    normalizedCoefficientCandidate17, rbMul17, rbNeg17, RationalBall.neg,
    RationalBall.mul, RationalBall.point]
private theorem evenBBall17_refines :
    |evenBBall17.center - evenBCoarse17.center| + evenBBall17.radius ≤
      evenBCoarse17.radius := by
  norm_num [evenBBall17, evenBCoarse17, roundedEvenBall30, cb17,
    normalizedCoefficientCandidate17, rbMul17, rbScale17, RationalBall.mul,
    RationalBall.point]
private theorem evenEBall17_refines :
    |evenEBall17.center - evenECoarse17.center| + evenEBall17.radius ≤
      evenECoarse17.radius := by
  norm_num [evenEBall17, evenECoarse17, roundedEvenBall30, cb17,
    normalizedCoefficientCandidate17, rbMul17, rbScale17, RationalBall.mul,
    RationalBall.point]
private theorem evenDBall17_refines :
    |evenDBall17.center - evenDCoarse17.center| + evenDBall17.radius ≤
      evenDCoarse17.radius := by
  norm_num [evenDBall17, evenEBall17, evenDCoarse17, roundedEvenBall30, cb17,
    normalizedCoefficientCandidate17, rbMul17, rbSub17, rbScale17,
    RationalBall.sub, RationalBall.add, RationalBall.neg, RationalBall.mul,
    RationalBall.point]
private theorem evenFBall17_refines :
    |evenFBall17.center - evenFCoarse17.center| + evenFBall17.radius ≤
      evenFCoarse17.radius := by
  norm_num [evenFBall17, evenFCoarse17, roundedEvenBall30, cb17,
    normalizedCoefficientCandidate17, rbMul17, rbSub17, rbScale17,
    RationalBall.sub, RationalBall.add, RationalBall.neg, RationalBall.mul,
    RationalBall.point]
private theorem evenGBall17_refines :
    |evenGBall17.center - evenGCoarse17.center| + evenGBall17.radius ≤
      evenGCoarse17.radius := by
  norm_num [evenGBall17, evenGCoarse17, roundedEvenBall30, cb17,
    normalizedCoefficientCandidate17, rbMul17, rbSub17, rbScale17,
    RationalBall.sub, RationalBall.add, RationalBall.neg, RationalBall.mul,
    RationalBall.point]
private theorem evenHBall17_refines :
    |evenHBall17.center - evenHCoarse17.center| + evenHBall17.radius ≤
      evenHCoarse17.radius := by
  norm_num [evenHBall17, evenHCoarse17, roundedEvenBall30, cb17,
    normalizedCoefficientCandidate17, rbMul17, rbScale17, RationalBall.mul,
    RationalBall.point]
private theorem evenIBall17_refines :
    |evenIBall17.center - evenICoarse17.center| + evenIBall17.radius ≤
      evenICoarse17.radius := by
  norm_num [evenIBall17, evenICoarse17, roundedEvenBall30, cb17,
    normalizedCoefficientCandidate17, rbMul17, rbSub17, rbScale17,
    RationalBall.sub, RationalBall.add, RationalBall.neg, RationalBall.mul,
    RationalBall.point]
private theorem evenJBall17_refines :
    |evenJBall17.center - evenJCoarse17.center| + evenJBall17.radius ≤
      evenJCoarse17.radius := by
  norm_num [evenJBall17, evenJCoarse17, roundedEvenBall30, cb17,
    normalizedCoefficientCandidate17, rbMul17, rbSub17, rbScale17,
    RationalBall.sub, RationalBall.add, RationalBall.neg, RationalBall.mul,
    RationalBall.point]
private theorem evenKBall17_refines :
    |evenKBall17.center - evenKCoarse17.center| + evenKBall17.radius ≤
      evenKCoarse17.radius := by
  norm_num [evenKBall17, evenKCoarse17, roundedEvenBall30, cb17,
    normalizedCoefficientCandidate17, rbMul17, rbSub17, rbScale17,
    RationalBall.sub, RationalBall.add, RationalBall.neg, RationalBall.mul,
    RationalBall.point]

private theorem even_coarse_component_balls17_contains (c : Fin 9 → ℝ)
    (hc : ∀ j, (cb17 j).Contains (c j)) :
    evenACoarse17.Contains (evenAReal17 c) ∧
    evenBCoarse17.Contains (evenBReal17 c) ∧
    evenECoarse17.Contains (evenEReal17 c) ∧
    evenDCoarse17.Contains (evenDReal17 c) ∧
    evenFCoarse17.Contains (evenFReal17 c) ∧
    evenGCoarse17.Contains (evenGReal17 c) ∧
    evenHCoarse17.Contains (evenHReal17 c) ∧
    evenICoarse17.Contains (evenIReal17 c) ∧
    evenJCoarse17.Contains (evenJReal17 c) ∧
    evenKCoarse17.Contains (evenKReal17 c) := by
  rcases even_component_balls17_contains c hc with
    ⟨ha, hb, he, hd, hf, hg, hh, hi, hj, hk⟩
  exact ⟨RationalBall.refine_contains17 evenABall17_refines ha,
    RationalBall.refine_contains17 evenBBall17_refines hb,
    RationalBall.refine_contains17 evenEBall17_refines he,
    RationalBall.refine_contains17 evenDBall17_refines hd,
    RationalBall.refine_contains17 evenFBall17_refines hf,
    RationalBall.refine_contains17 evenGBall17_refines hg,
    RationalBall.refine_contains17 evenHBall17_refines hh,
    RationalBall.refine_contains17 evenIBall17_refines hi,
    RationalBall.refine_contains17 evenJBall17_refines hj,
    RationalBall.refine_contains17 evenKBall17_refines hk⟩

private theorem evenDetACalc17_refines :
    |evenDetACalc17.center - evenDetACoarse17.center| + evenDetACalc17.radius ≤
      evenDetACoarse17.radius := by
  norm_num [evenDetACalc17, evenDetACoarse17, roundedEvenBall30, roundedEvenBall35,
    evenACoarse17, evenBCoarse17, evenECoarse17, evenDCoarse17,
    evenFCoarse17, evenGCoarse17, rbAdd17, rbSub17, rbMul17, rbScale17,
    RationalBall.add, RationalBall.sub, RationalBall.neg, RationalBall.mul,
    RationalBall.point]
private theorem evenEnergyCalc17_refines :
    |evenEnergyCalc17.center - evenEnergyCoarse17.center| + evenEnergyCalc17.radius ≤
      evenEnergyCoarse17.radius := by
  norm_num [evenEnergyCalc17, evenEnergyCoarse17, roundedEvenBall30, roundedEvenBall35,
    evenACoarse17, evenBCoarse17, evenECoarse17, evenDCoarse17,
    evenFCoarse17, evenGCoarse17, evenHCoarse17, evenICoarse17, evenJCoarse17,
    evenKCoarse17, evenU0Ball17, evenU1Ball17, evenU2Ball17, evenU0Q17,
    evenU1Q17, evenU2Q17, rbAdd17, rbSub17, rbMul17, rbScale17,
    RationalBall.add, RationalBall.sub, RationalBall.neg, RationalBall.mul,
    RationalBall.point]
private theorem evenR0Calc17_refines :
    |evenR0Calc17.center - evenR0Coarse17.center| + evenR0Calc17.radius ≤
      evenR0Coarse17.radius := by
  norm_num [evenR0Calc17, evenR0Coarse17, roundedEvenBall30, roundedEvenBall35,
    evenACoarse17, evenBCoarse17, evenECoarse17, evenHCoarse17,
    evenU0Ball17, evenU1Ball17, evenU2Ball17, evenU0Q17, evenU1Q17,
    evenU2Q17, rbAdd17, rbMul17, rbScale17, RationalBall.add,
    RationalBall.neg, RationalBall.mul, RationalBall.point]
private theorem evenR1Calc17_refines :
    |evenR1Calc17.center - evenR1Coarse17.center| + evenR1Calc17.radius ≤
      evenR1Coarse17.radius := by
  norm_num [evenR1Calc17, evenR1Coarse17, roundedEvenBall30, roundedEvenBall35,
    evenBCoarse17, evenDCoarse17, evenFCoarse17, evenICoarse17,
    evenU0Ball17, evenU1Ball17, evenU2Ball17, evenU0Q17, evenU1Q17,
    evenU2Q17, rbAdd17, rbMul17, rbScale17, RationalBall.add,
    RationalBall.neg, RationalBall.mul, RationalBall.point]
private theorem evenR2Calc17_refines :
    |evenR2Calc17.center - evenR2Coarse17.center| + evenR2Calc17.radius ≤
      evenR2Coarse17.radius := by
  norm_num [evenR2Calc17, evenR2Coarse17, roundedEvenBall30, roundedEvenBall35,
    evenECoarse17, evenFCoarse17, evenGCoarse17, evenJCoarse17,
    evenU0Ball17, evenU1Ball17, evenU2Ball17, evenU0Q17, evenU1Q17,
    evenU2Q17, rbAdd17, rbMul17, rbScale17, RationalBall.add,
    RationalBall.neg, RationalBall.mul, RationalBall.point]
private theorem evenAdjQuadCalc17_refines :
    |evenAdjQuadCalc17.center - evenAdjQuadCoarse17.center| + evenAdjQuadCalc17.radius ≤
      evenAdjQuadCoarse17.radius := by
  norm_num [evenAdjQuadCalc17, evenAdjQuadCoarse17, roundedEvenBall30,
    roundedEvenBall35, roundedEvenBall50,
    evenACoarse17, evenBCoarse17, evenECoarse17, evenDCoarse17,
    evenFCoarse17, evenGCoarse17, evenR0Coarse17, evenR1Coarse17,
    evenR2Coarse17, rbAdd17, rbSub17, rbMul17, rbScale17,
    RationalBall.add, RationalBall.sub, RationalBall.neg, RationalBall.mul,
    RationalBall.point]
private theorem evenGateCalc17_refines :
    |evenGateCalc17.center - evenGateCoarse17.center| + evenGateCalc17.radius ≤
      evenGateCoarse17.radius := by
  norm_num [evenGateCalc17, evenGateCoarse17, roundedEvenBall30,
    roundedEvenBall35, roundedEvenBall50,
    evenDetACoarse17, evenEnergyCoarse17, evenAdjQuadCoarse17,
    rbSub17, rbMul17, RationalBall.sub, RationalBall.add,
    RationalBall.neg, RationalBall.mul, RationalBall.point]

private theorem evenDetACalc17_contains (c : Fin 9 → ℝ)
    (ha : evenACoarse17.Contains (evenAReal17 c))
    (hb : evenBCoarse17.Contains (evenBReal17 c))
    (he : evenECoarse17.Contains (evenEReal17 c))
    (hd : evenDCoarse17.Contains (evenDReal17 c))
    (hf : evenFCoarse17.Contains (evenFReal17 c))
    (hg : evenGCoarse17.Contains (evenGReal17 c)) :
    evenDetACalc17.Contains
      (evenDetAReal17 (evenAReal17 c) (evenBReal17 c) (evenEReal17 c)
        (evenDReal17 c) (evenFReal17 c) (evenGReal17 c)) := by
  dsimp [evenDetACalc17, evenDetAReal17, rbAdd17, rbSub17, rbMul17, rbScale17]
  repeat first
    | assumption
    | exact RationalBall.point_contains _
    | apply RationalBall.add_contains
    | apply RationalBall.sub_contains
    | apply RationalBall.neg_contains
    | apply RationalBall.mul_contains

private theorem evenEnergyCalc17_contains (c : Fin 9 → ℝ)
    (ha : evenACoarse17.Contains (evenAReal17 c))
    (hb : evenBCoarse17.Contains (evenBReal17 c))
    (he : evenECoarse17.Contains (evenEReal17 c))
    (hd : evenDCoarse17.Contains (evenDReal17 c))
    (hf : evenFCoarse17.Contains (evenFReal17 c))
    (hg : evenGCoarse17.Contains (evenGReal17 c))
    (hh : evenHCoarse17.Contains (evenHReal17 c))
    (hi : evenICoarse17.Contains (evenIReal17 c))
    (hj : evenJCoarse17.Contains (evenJReal17 c))
    (hk : evenKCoarse17.Contains (evenKReal17 c)) :
    evenEnergyCalc17.Contains
      (evenEnergyReal17 (evenAReal17 c) (evenBReal17 c) (evenEReal17 c)
        (evenDReal17 c) (evenFReal17 c) (evenGReal17 c)
        (evenHReal17 c) (evenIReal17 c) (evenJReal17 c) (evenKReal17 c)) := by
  have hu0 : evenU0Ball17.Contains evenU0Real17 := by
    exact_mod_cast RationalBall.point_contains evenU0Q17
  have hu1 : evenU1Ball17.Contains evenU1Real17 := by
    exact_mod_cast RationalBall.point_contains evenU1Q17
  have hu2 : evenU2Ball17.Contains evenU2Real17 := by
    exact_mod_cast RationalBall.point_contains evenU2Q17
  dsimp [evenEnergyCalc17, evenEnergyReal17, rbAdd17, rbSub17, rbMul17, rbScale17]
  repeat first
    | assumption
    | exact RationalBall.point_contains _
    | apply RationalBall.add_contains
    | apply RationalBall.sub_contains
    | apply RationalBall.neg_contains
    | apply RationalBall.mul_contains

private theorem evenR0Calc17_contains (c : Fin 9 → ℝ)
    (ha : evenACoarse17.Contains (evenAReal17 c))
    (hb : evenBCoarse17.Contains (evenBReal17 c))
    (he : evenECoarse17.Contains (evenEReal17 c))
    (hh : evenHCoarse17.Contains (evenHReal17 c)) :
    evenR0Calc17.Contains
      (evenR0Real17 (evenAReal17 c) (evenBReal17 c) (evenEReal17 c) (evenHReal17 c)) := by
  have hu0 : evenU0Ball17.Contains evenU0Real17 := by
    exact_mod_cast RationalBall.point_contains evenU0Q17
  have hu1 : evenU1Ball17.Contains evenU1Real17 := by
    exact_mod_cast RationalBall.point_contains evenU1Q17
  have hu2 : evenU2Ball17.Contains evenU2Real17 := by
    exact_mod_cast RationalBall.point_contains evenU2Q17
  dsimp [evenR0Calc17, evenR0Real17, rbAdd17, rbSub17, rbMul17, rbScale17]
  repeat first
    | assumption
    | exact RationalBall.point_contains _
    | apply RationalBall.add_contains
    | apply RationalBall.sub_contains
    | apply RationalBall.neg_contains
    | apply RationalBall.mul_contains

private theorem evenR1Calc17_contains (c : Fin 9 → ℝ)
    (hb : evenBCoarse17.Contains (evenBReal17 c))
    (hd : evenDCoarse17.Contains (evenDReal17 c))
    (hf : evenFCoarse17.Contains (evenFReal17 c))
    (hi : evenICoarse17.Contains (evenIReal17 c)) :
    evenR1Calc17.Contains
      (evenR1Real17 (evenBReal17 c) (evenDReal17 c) (evenFReal17 c) (evenIReal17 c)) := by
  have hu0 : evenU0Ball17.Contains evenU0Real17 := by
    exact_mod_cast RationalBall.point_contains evenU0Q17
  have hu1 : evenU1Ball17.Contains evenU1Real17 := by
    exact_mod_cast RationalBall.point_contains evenU1Q17
  have hu2 : evenU2Ball17.Contains evenU2Real17 := by
    exact_mod_cast RationalBall.point_contains evenU2Q17
  dsimp [evenR1Calc17, evenR1Real17, rbAdd17, rbSub17, rbMul17, rbScale17]
  repeat first
    | assumption
    | exact RationalBall.point_contains _
    | apply RationalBall.add_contains
    | apply RationalBall.sub_contains
    | apply RationalBall.neg_contains
    | apply RationalBall.mul_contains

private theorem evenR2Calc17_contains (c : Fin 9 → ℝ)
    (he : evenECoarse17.Contains (evenEReal17 c))
    (hf : evenFCoarse17.Contains (evenFReal17 c))
    (hg : evenGCoarse17.Contains (evenGReal17 c))
    (hj : evenJCoarse17.Contains (evenJReal17 c)) :
    evenR2Calc17.Contains
      (evenR2Real17 (evenEReal17 c) (evenFReal17 c) (evenGReal17 c) (evenJReal17 c)) := by
  have hu0 : evenU0Ball17.Contains evenU0Real17 := by
    exact_mod_cast RationalBall.point_contains evenU0Q17
  have hu1 : evenU1Ball17.Contains evenU1Real17 := by
    exact_mod_cast RationalBall.point_contains evenU1Q17
  have hu2 : evenU2Ball17.Contains evenU2Real17 := by
    exact_mod_cast RationalBall.point_contains evenU2Q17
  dsimp [evenR2Calc17, evenR2Real17, rbAdd17, rbSub17, rbMul17, rbScale17]
  repeat first
    | assumption
    | exact RationalBall.point_contains _
    | apply RationalBall.add_contains
    | apply RationalBall.sub_contains
    | apply RationalBall.neg_contains
    | apply RationalBall.mul_contains

private theorem evenAdjQuadCalc17_contains (c : Fin 9 → ℝ)
    (ha : evenACoarse17.Contains (evenAReal17 c))
    (hb : evenBCoarse17.Contains (evenBReal17 c))
    (he : evenECoarse17.Contains (evenEReal17 c))
    (hd : evenDCoarse17.Contains (evenDReal17 c))
    (hf : evenFCoarse17.Contains (evenFReal17 c))
    (hg : evenGCoarse17.Contains (evenGReal17 c))
    (hr0 : evenR0Coarse17.Contains
      (evenR0Real17 (evenAReal17 c) (evenBReal17 c) (evenEReal17 c) (evenHReal17 c)))
    (hr1 : evenR1Coarse17.Contains
      (evenR1Real17 (evenBReal17 c) (evenDReal17 c) (evenFReal17 c) (evenIReal17 c)))
    (hr2 : evenR2Coarse17.Contains
      (evenR2Real17 (evenEReal17 c) (evenFReal17 c) (evenGReal17 c) (evenJReal17 c))) :
    evenAdjQuadCalc17.Contains
      (evenAdjQuadReal17 (evenAReal17 c) (evenBReal17 c) (evenEReal17 c)
        (evenDReal17 c) (evenFReal17 c) (evenGReal17 c)
        (evenR0Real17 (evenAReal17 c) (evenBReal17 c) (evenEReal17 c) (evenHReal17 c))
        (evenR1Real17 (evenBReal17 c) (evenDReal17 c) (evenFReal17 c) (evenIReal17 c))
        (evenR2Real17 (evenEReal17 c) (evenFReal17 c) (evenGReal17 c) (evenJReal17 c))) := by
  dsimp [evenAdjQuadCalc17, evenAdjQuadReal17, rbAdd17, rbSub17, rbMul17, rbScale17]
  repeat first
    | assumption
    | exact RationalBall.point_contains _
    | apply RationalBall.add_contains
    | apply RationalBall.sub_contains
    | apply RationalBall.neg_contains
    | apply RationalBall.mul_contains

private theorem evenGateCalc17_contains (c : Fin 9 → ℝ)
    (hdet : evenDetACoarse17.Contains
      (evenDetAReal17 (evenAReal17 c) (evenBReal17 c) (evenEReal17 c)
        (evenDReal17 c) (evenFReal17 c) (evenGReal17 c)))
    (henergy : evenEnergyCoarse17.Contains
      (evenEnergyReal17 (evenAReal17 c) (evenBReal17 c) (evenEReal17 c)
        (evenDReal17 c) (evenFReal17 c) (evenGReal17 c)
        (evenHReal17 c) (evenIReal17 c) (evenJReal17 c) (evenKReal17 c)))
    (hadj : evenAdjQuadCoarse17.Contains
      (evenAdjQuadReal17 (evenAReal17 c) (evenBReal17 c) (evenEReal17 c)
        (evenDReal17 c) (evenFReal17 c) (evenGReal17 c)
        (evenR0Real17 (evenAReal17 c) (evenBReal17 c) (evenEReal17 c) (evenHReal17 c))
        (evenR1Real17 (evenBReal17 c) (evenDReal17 c) (evenFReal17 c) (evenIReal17 c))
        (evenR2Real17 (evenEReal17 c) (evenFReal17 c) (evenGReal17 c) (evenJReal17 c)))) :
    evenGateCalc17.Contains
      (evenGateReal17 (evenAReal17 c) (evenBReal17 c) (evenEReal17 c)
        (evenDReal17 c) (evenFReal17 c) (evenGReal17 c)
        (evenHReal17 c) (evenIReal17 c) (evenJReal17 c) (evenKReal17 c)) := by
  simpa [evenGateCalc17, evenGateReal17, rbSub17, rbMul17,
    RationalBall.sub] using RationalBall.sub_contains (RationalBall.mul_contains hdet henergy) hadj

private theorem even_cofactor_gate_ball17_contains (c : Fin 9 → ℝ)
    (hc : ∀ j, (cb17 j).Contains (c j)) :
    evenGateCoarse17.Contains
      (evenGateReal17 (evenAReal17 c) (evenBReal17 c) (evenEReal17 c)
        (evenDReal17 c) (evenFReal17 c) (evenGReal17 c)
        (evenHReal17 c) (evenIReal17 c) (evenJReal17 c) (evenKReal17 c)) := by
  rcases even_coarse_component_balls17_contains c hc with
    ⟨ha, hb, he, hd, hf, hg, hh, hi, hj, hk⟩
  have hdetCalc := evenDetACalc17_contains c ha hb he hd hf hg
  have henergyCalc := evenEnergyCalc17_contains c ha hb he hd hf hg hh hi hj hk
  have hr0Calc := evenR0Calc17_contains c ha hb he hh
  have hr1Calc := evenR1Calc17_contains c hb hd hf hi
  have hr2Calc := evenR2Calc17_contains c he hf hg hj
  have hdet := RationalBall.refine_contains17 evenDetACalc17_refines hdetCalc
  have henergy := RationalBall.refine_contains17 evenEnergyCalc17_refines henergyCalc
  have hr0 := RationalBall.refine_contains17 evenR0Calc17_refines hr0Calc
  have hr1 := RationalBall.refine_contains17 evenR1Calc17_refines hr1Calc
  have hr2 := RationalBall.refine_contains17 evenR2Calc17_refines hr2Calc
  have hadjCalc := evenAdjQuadCalc17_contains c ha hb he hd hf hg hr0 hr1 hr2
  have hadj := RationalBall.refine_contains17 evenAdjQuadCalc17_refines hadjCalc
  have hgateCalc := evenGateCalc17_contains c hdet henergy hadj
  exact RationalBall.refine_contains17 evenGateCalc17_refines hgateCalc

private theorem even_cofactor_gate_ball17_lower :
    (0 : ℚ) < evenGateCoarse17.center - evenGateCoarse17.radius := by
  decide +kernel

theorem native_normalized_even_fourth_cofactor_gate17 :
    0 < evenGateReal17
      (evenAReal17 normalizedNativeCoefficient17)
      (evenBReal17 normalizedNativeCoefficient17)
      (evenEReal17 normalizedNativeCoefficient17)
      (evenDReal17 normalizedNativeCoefficient17)
      (evenFReal17 normalizedNativeCoefficient17)
      (evenGReal17 normalizedNativeCoefficient17)
      (evenHReal17 normalizedNativeCoefficient17)
      (evenIReal17 normalizedNativeCoefficient17)
      (evenJReal17 normalizedNativeCoefficient17)
      (evenKReal17 normalizedNativeCoefficient17) := by
  have hbox := even_cofactor_gate_ball17_contains normalizedNativeCoefficient17
    normalized_native_coefficient17_contains
  have hlower := RationalBall.lower_le_of_contains hbox
  have hpositive : (0 : ℚ) < evenGateCoarse17.center - evenGateCoarse17.radius :=
    even_cofactor_gate_ball17_lower
  exact lt_of_lt_of_le (by exact_mod_cast hpositive) hlower

def evenFourthB17 (c : Fin 9 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![evenAReal17 c, evenBReal17 c, evenEReal17 c, evenHReal17 c;
     evenBReal17 c, evenDReal17 c, evenFReal17 c, evenIReal17 c;
     evenEReal17 c, evenFReal17 c, evenGReal17 c, evenJReal17 c;
     evenHReal17 c, evenIReal17 c, evenJReal17 c, evenKReal17 c]

private theorem even_fourth_border_identity17 (c : Fin 9 → ℝ) :
    evenFourthB17 c = C3GeneralCofactor.border
      (!![evenAReal17 c, evenBReal17 c, evenEReal17 c;
          evenBReal17 c, evenDReal17 c, evenFReal17 c;
          evenEReal17 c, evenFReal17 c, evenGReal17 c] : Matrix (Fin 3) (Fin 3) ℝ)
      (![evenHReal17 c, evenIReal17 c, evenJReal17 c] : Fin 3 → ℝ)
      (evenKReal17 c) := by
  ext x y
  cases x using Fin.lastCases with
  | last =>
    cases y using Fin.lastCases with
    | last =>
      rw [C3GeneralCofactor.border_last_last]
      simp [evenFourthB17, evenKReal17]
    | cast j =>
      rw [C3GeneralCofactor.border_last_castSucc]
      fin_cases j <;> simp [evenFourthB17, evenHReal17, evenIReal17, evenJReal17]
  | cast i =>
    cases y using Fin.lastCases with
    | last =>
      rw [C3GeneralCofactor.border_castSucc_last]
      fin_cases i <;> simp [evenFourthB17, evenHReal17, evenIReal17, evenJReal17]
    | cast j =>
      rw [C3GeneralCofactor.border_castSucc_castSucc]
      fin_cases i <;> fin_cases j
      all_goals
        simp [evenFourthB17, evenAReal17, evenBReal17, evenEReal17,
          evenDReal17, evenFReal17, evenGReal17]

private theorem even_gate_border_identity17 (a b e d f g h i j k : ℝ) :
    evenGateReal17 a b e d f g h i j k =
      (C3GeneralCofactor.border
        (!![a, b, e; b, d, f; e, f, g] : Matrix (Fin 3) (Fin 3) ℝ)
        (![h, i, j] : Fin 3 → ℝ) k).det := by
  let A : Matrix (Fin 3) (Fin 3) ℝ := !![a, b, e; b, d, f; e, f, g]
  let q : Fin 3 → ℝ := ![h, i, j]
  let u : Fin 3 → ℝ := ![evenU0Real17, evenU1Real17, evenU2Real17]
  have hsym : A.transpose = A := by
    ext x y
    fin_cases x <;> fin_cases y <;> simp [A]
  have hdet : evenDetAReal17 a b e d f g = A.det := by
    simp [A, evenDetAReal17, Matrix.det_fin_three]
    ring
  have henergy : evenEnergyReal17 a b e d f g h i j k =
      C3GeneralCofactor.directionalEnergy A q k u := by
    simp [evenEnergyReal17, C3GeneralCofactor.directionalEnergy, A, q, u,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      evenU0Real17, evenU1Real17, evenU2Real17]
    ring
  have hres : evenAdjQuadReal17 a b e d f g
        (evenR0Real17 a b e h) (evenR1Real17 b d f i) (evenR2Real17 e f g j) =
      dotProduct (C3GeneralCofactor.directionalResidual A q u)
        (A.adjugate.mulVec (C3GeneralCofactor.directionalResidual A q u)) := by
    simp [evenAdjQuadReal17, evenR0Real17, evenR1Real17, evenR2Real17,
      C3GeneralCofactor.directionalResidual, A, q, u,
      Matrix.adjugate_fin_three_of, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, evenU0Real17, evenU1Real17, evenU2Real17]
    ring
  have hborder := C3GeneralCofactor.border_directional_identity A q k u hsym
  dsimp [evenGateReal17]
  rw [hdet, henergy, hres]
  exact hborder

theorem native_normalized_even_fourth_determinant_eq_gate17 :
    (evenFourthB17 normalizedNativeCoefficient17).det =
      evenGateReal17
        (evenAReal17 normalizedNativeCoefficient17)
        (evenBReal17 normalizedNativeCoefficient17)
        (evenEReal17 normalizedNativeCoefficient17)
        (evenDReal17 normalizedNativeCoefficient17)
        (evenFReal17 normalizedNativeCoefficient17)
        (evenGReal17 normalizedNativeCoefficient17)
        (evenHReal17 normalizedNativeCoefficient17)
        (evenIReal17 normalizedNativeCoefficient17)
        (evenJReal17 normalizedNativeCoefficient17)
        (evenKReal17 normalizedNativeCoefficient17) := by
  rw [even_fourth_border_identity17]
  exact (even_gate_border_identity17
    (evenAReal17 normalizedNativeCoefficient17)
    (evenBReal17 normalizedNativeCoefficient17)
    (evenEReal17 normalizedNativeCoefficient17)
    (evenDReal17 normalizedNativeCoefficient17)
    (evenFReal17 normalizedNativeCoefficient17)
    (evenGReal17 normalizedNativeCoefficient17)
    (evenHReal17 normalizedNativeCoefficient17)
    (evenIReal17 normalizedNativeCoefficient17)
    (evenJReal17 normalizedNativeCoefficient17)
    (evenKReal17 normalizedNativeCoefficient17)).symm

end
end C3ShiftedFourth
