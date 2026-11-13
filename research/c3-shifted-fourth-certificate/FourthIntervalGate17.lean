import FourthGate17
import FourthSourceGate17
import GeneralCofactorIdentity
import Mathlib.LinearAlgebra.Matrix.Adjugate

namespace C3ShiftedFourth

open C3Cofactor C3GeneralCofactor CarryC3Boxes CarryC3Tail CarryC3Gamma
  CarrySelfAdjointOperator PhysicalSewing CarryTwoEvenJets
  C3CofactorCorrelation CarrySourceBezout
open scoped BigOperators Matrix

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 30000000
set_option maxRecDepth 30000

private def rbAdd (a b : RationalBall) : RationalBall := a.add b
private def rbSub (a b : RationalBall) : RationalBall := a.sub b
private def rbMul (a b : RationalBall) : RationalBall := a.mul b
private def rbScale (q : ℚ) (a : RationalBall) : RationalBall :=
  RationalBall.point q |>.mul a

private def normCoeffBall17 (j : Fin 9) : RationalBall :=
  normalizedCoefficientCandidate17 j

private def oddAReal17 (c : Fin 9 → ℝ) := c 1 * c 1 - 2 * (c 0 * c 2)
private def oddBReal17 (c : Fin 9 → ℝ) := c 1 * c 2 - 3 * (c 0 * c 3)
private def oddEReal17 (c : Fin 9 → ℝ) := c 1 * c 3 - 4 * (c 0 * c 4)
private def oddHReal17 (c : Fin 9 → ℝ) := c 1 * c 4 - 5 * (c 0 * c 5)
private def oddDReal17 (c : Fin 9 → ℝ) :=
  2 * (c 2 * c 2) - 2 * (c 1 * c 3) - 4 * (c 0 * c 4)
private def oddFReal17 (c : Fin 9 → ℝ) :=
  2 * (c 2 * c 3) - 3 * (c 1 * c 4) - 5 * (c 0 * c 5)
private def oddIReal17 (c : Fin 9 → ℝ) :=
  2 * (c 2 * c 4) - 4 * (c 1 * c 5) - 6 * (c 0 * c 6)
private def oddGReal17 (c : Fin 9 → ℝ) :=
  3 * (c 3 * c 3) - 2 * (c 2 * c 4) - 4 * (c 1 * c 5) - 6 * (c 0 * c 6)
private def oddJReal17 (c : Fin 9 → ℝ) :=
  3 * (c 3 * c 4) - 3 * (c 2 * c 5) - 5 * (c 1 * c 6) - 7 * (c 0 * c 7)
private def oddKReal17 (c : Fin 9 → ℝ) :=
  4 * (c 4 * c 4) - 2 * (c 3 * c 5) - 4 * (c 2 * c 6) -
    6 * (c 1 * c 7) - 8 * (c 0 * c 8)

private def oddABall17 :=
  rbSub (rbMul (normCoeffBall17 1) (normCoeffBall17 1))
    (rbScale 2 (rbMul (normCoeffBall17 0) (normCoeffBall17 2)))
private def oddBBall17 :=
  rbSub (rbMul (normCoeffBall17 1) (normCoeffBall17 2))
    (rbScale 3 (rbMul (normCoeffBall17 0) (normCoeffBall17 3)))
private def oddEBall17 :=
  rbSub (rbMul (normCoeffBall17 1) (normCoeffBall17 3))
    (rbScale 4 (rbMul (normCoeffBall17 0) (normCoeffBall17 4)))
private def oddHBall17 :=
  rbSub (rbMul (normCoeffBall17 1) (normCoeffBall17 4))
    (rbScale 5 (rbMul (normCoeffBall17 0) (normCoeffBall17 5)))
private def oddDBall17 :=
  rbSub (rbSub (rbScale 2 (rbMul (normCoeffBall17 2) (normCoeffBall17 2)))
    (rbScale 2 (rbMul (normCoeffBall17 1) (normCoeffBall17 3))))
    (rbScale 4 (rbMul (normCoeffBall17 0) (normCoeffBall17 4)))
private def oddFBall17 :=
  rbSub (rbSub (rbScale 2 (rbMul (normCoeffBall17 2) (normCoeffBall17 3)))
    (rbScale 3 (rbMul (normCoeffBall17 1) (normCoeffBall17 4))))
    (rbScale 5 (rbMul (normCoeffBall17 0) (normCoeffBall17 5)))
private def oddIBall17 :=
  rbSub (rbSub (rbScale 2 (rbMul (normCoeffBall17 2) (normCoeffBall17 4)))
    (rbScale 4 (rbMul (normCoeffBall17 1) (normCoeffBall17 5))))
    (rbScale 6 (rbMul (normCoeffBall17 0) (normCoeffBall17 6)))
private def oddGBall17 :=
  rbSub (rbSub (rbSub (rbScale 3 (rbMul (normCoeffBall17 3) (normCoeffBall17 3)))
    (rbScale 2 (rbMul (normCoeffBall17 2) (normCoeffBall17 4))))
    (rbScale 4 (rbMul (normCoeffBall17 1) (normCoeffBall17 5))))
    (rbScale 6 (rbMul (normCoeffBall17 0) (normCoeffBall17 6)))
private def oddJBall17 :=
  rbSub (rbSub (rbSub (rbScale 3 (rbMul (normCoeffBall17 3) (normCoeffBall17 4)))
    (rbScale 3 (rbMul (normCoeffBall17 2) (normCoeffBall17 5))))
    (rbScale 5 (rbMul (normCoeffBall17 1) (normCoeffBall17 6))))
    (rbScale 7 (rbMul (normCoeffBall17 0) (normCoeffBall17 7)))
private def oddKBall17 :=
  rbSub (rbSub (rbSub (rbSub (rbScale 4 (rbMul (normCoeffBall17 4) (normCoeffBall17 4)))
    (rbScale 2 (rbMul (normCoeffBall17 3) (normCoeffBall17 5))))
    (rbScale 4 (rbMul (normCoeffBall17 2) (normCoeffBall17 6))))
    (rbScale 6 (rbMul (normCoeffBall17 1) (normCoeffBall17 7))))
    (rbScale 8 (rbMul (normCoeffBall17 0) (normCoeffBall17 8)))

private theorem odd_component_balls17_contains (c : Fin 9 → ℝ)
    (hc : ∀ j, (normCoeffBall17 j).Contains (c j)) :
    (oddABall17.Contains (oddAReal17 c)) ∧
    (oddBBall17.Contains (oddBReal17 c)) ∧
    (oddEBall17.Contains (oddEReal17 c)) ∧
    (oddHBall17.Contains (oddHReal17 c)) ∧
    (oddDBall17.Contains (oddDReal17 c)) ∧
    (oddFBall17.Contains (oddFReal17 c)) ∧
    (oddIBall17.Contains (oddIReal17 c)) ∧
    (oddGBall17.Contains (oddGReal17 c)) ∧
    (oddJBall17.Contains (oddJReal17 c)) ∧
    (oddKBall17.Contains (oddKReal17 c)) := by
  have h0 := hc 0
  have h1 := hc 1
  have h2 := hc 2
  have h3 := hc 3
  have h4 := hc 4
  have h5 := hc 5
  have h6 := hc 6
  have h7 := hc 7
  have h8 := hc 8
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [oddABall17, oddBBall17, oddEBall17, oddHBall17, oddDBall17,
      oddFBall17, oddIBall17, oddGBall17, oddJBall17, oddKBall17,
      oddAReal17, oddBReal17, oddEReal17, oddHReal17, oddDReal17,
      oddFReal17, oddIReal17, oddGReal17, oddJReal17, oddKReal17,
      normCoeffBall17, rbSub, rbMul, rbScale, RationalBall.sub,
      sub_eq_add_neg] <;>
    repeat first
      | assumption
      | exact RationalBall.point_contains _
      | apply RationalBall.add_contains
      | apply RationalBall.neg_contains
      | apply RationalBall.mul_contains

private def u0Ball17 : RationalBall := RationalBall.point
  (687319496278479 / 10^21)
private def u1Ball17 : RationalBall := RationalBall.point
  (62201005107449897 / (5 * 10^20))
private def u2Ball17 : RationalBall := RationalBall.point
  (7763303426381202809 / (5 * 10^20))
private def u0Real17 : ℝ := 687319496278479 / 10^21
private def u1Real17 : ℝ := 62201005107449897 / (5 * 10^20)
private def u2Real17 : ℝ := 7763303426381202809 / (5 * 10^20)

private def detAReal17 (a b e d f g : ℝ) :=
  (a*d)*g + 2*((b*e)*f) - a*(f*f) - d*(e*e) - g*(b*b)
private def energyReal17 (a b e d f g h i j k : ℝ) :=
  a*(u0Real17*u0Real17) + (2*b)*(u0Real17*u1Real17) +
    (2*e)*(u0Real17*u2Real17) + d*(u1Real17*u1Real17) +
    (2*f)*(u1Real17*u2Real17) + g*(u2Real17*u2Real17) +
    (2*h)*u0Real17 + (2*i)*u1Real17 + (2*j)*u2Real17 + k
private def r0Real17 (a b e h : ℝ) := a*u0Real17 + b*u1Real17 + e*u2Real17 + h
private def r1Real17 (b d f i : ℝ) := b*u0Real17 + d*u1Real17 + f*u2Real17 + i
private def r2Real17 (e f g j : ℝ) := e*u0Real17 + f*u1Real17 + g*u2Real17 + j
private def adjQuadReal17 (a b e d f g r0 r1 r2 : ℝ) :=
  (d*g-f*f)*(r0*r0) + (a*g-e*e)*(r1*r1) + (a*d-b*b)*(r2*r2) +
    (2*(e*f-b*g))*(r0*r1) + (2*(b*f-d*e))*(r0*r2) +
      (2*(b*e-a*f))*(r1*r2)
private def cofactorGateReal17 (a b e d f g h i j k : ℝ) :=
  detAReal17 a b e d f g * energyReal17 a b e d f g h i j k -
    adjQuadReal17 a b e d f g (r0Real17 a b e h)
      (r1Real17 b d f i) (r2Real17 e f g j)

private theorem cofactor_gate_border_identity17 (a b e d f g h i j k : ℝ) :
    cofactorGateReal17 a b e d f g h i j k =
      (C3GeneralCofactor.border
        (!![a, b, e; b, d, f; e, f, g] : Matrix (Fin 3) (Fin 3) ℝ)
        (![h, i, j] : Fin 3 → ℝ) k).det := by
  let A : Matrix (Fin 3) (Fin 3) ℝ := !![a, b, e; b, d, f; e, f, g]
  let q : Fin 3 → ℝ := ![h, i, j]
  let u : Fin 3 → ℝ := ![u0Real17, u1Real17, u2Real17]
  have hsym : A.transpose = A := by
    ext x y
    fin_cases x <;> fin_cases y <;> simp [A]
  have hdet : detAReal17 a b e d f g = A.det := by
    simp [A, detAReal17, Matrix.det_fin_three]
    ring
  have henergy : energyReal17 a b e d f g h i j k =
      C3GeneralCofactor.directionalEnergy A q k u := by
    simp [energyReal17, C3GeneralCofactor.directionalEnergy, A, q, u,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ, u0Real17, u1Real17, u2Real17]
    ring
  have hres : adjQuadReal17 a b e d f g
        (r0Real17 a b e h) (r1Real17 b d f i) (r2Real17 e f g j) =
      dotProduct (C3GeneralCofactor.directionalResidual A q u)
        (A.adjugate.mulVec (C3GeneralCofactor.directionalResidual A q u)) := by
    simp [adjQuadReal17, r0Real17, r1Real17, r2Real17,
      C3GeneralCofactor.directionalResidual, A, q, u,
      Matrix.adjugate_fin_three_of, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, u0Real17, u1Real17, u2Real17]
    ring
  have hborder := C3GeneralCofactor.border_directional_identity A q k u hsym
  dsimp [cofactorGateReal17]
  rw [hdet, henergy, hres]
  exact hborder

private theorem oddFourthB_border_identity17 (c : Fin 9 → ℝ) :
    oddFourthB c = C3GeneralCofactor.border
      (!![oddAReal17 c, oddBReal17 c, oddEReal17 c;
          oddBReal17 c, oddDReal17 c, oddFReal17 c;
          oddEReal17 c, oddFReal17 c, oddGReal17 c] : Matrix (Fin 3) (Fin 3) ℝ)
      (![oddHReal17 c, oddIReal17 c, oddJReal17 c] : Fin 3 → ℝ)
      (oddKReal17 c) := by
  ext x y
  cases x using Fin.lastCases with
  | last =>
    cases y using Fin.lastCases with
    | last =>
      rw [C3GeneralCofactor.border_last_last]
      simp [oddFourthB, oddKReal17]
      ring
    | cast j =>
      rw [C3GeneralCofactor.border_last_castSucc]
      fin_cases j <;> simp [oddFourthB, oddHReal17, oddIReal17, oddJReal17]
  | cast i =>
    cases y using Fin.lastCases with
    | last =>
      rw [C3GeneralCofactor.border_castSucc_last]
      fin_cases i <;> simp [oddFourthB, oddHReal17, oddIReal17, oddJReal17]
    | cast j =>
      rw [C3GeneralCofactor.border_castSucc_castSucc]
      fin_cases i <;> fin_cases j
      all_goals
        simp [oddFourthB, oddAReal17, oddBReal17, oddEReal17,
          oddDReal17, oddFReal17, oddGReal17]
        try ring

theorem native_normalized_fourth_determinant_eq_gate17 :
    (oddFourthB normalizedNativeCoefficient17).det =
      cofactorGateReal17
        (oddAReal17 normalizedNativeCoefficient17)
        (oddBReal17 normalizedNativeCoefficient17)
        (oddEReal17 normalizedNativeCoefficient17)
        (oddDReal17 normalizedNativeCoefficient17)
        (oddFReal17 normalizedNativeCoefficient17)
        (oddGReal17 normalizedNativeCoefficient17)
        (oddHReal17 normalizedNativeCoefficient17)
        (oddIReal17 normalizedNativeCoefficient17)
        (oddJReal17 normalizedNativeCoefficient17)
        (oddKReal17 normalizedNativeCoefficient17) := by
  rw [oddFourthB_border_identity17]
  exact (cofactor_gate_border_identity17
    (oddAReal17 normalizedNativeCoefficient17)
    (oddBReal17 normalizedNativeCoefficient17)
    (oddEReal17 normalizedNativeCoefficient17)
    (oddDReal17 normalizedNativeCoefficient17)
    (oddFReal17 normalizedNativeCoefficient17)
    (oddGReal17 normalizedNativeCoefficient17)
    (oddHReal17 normalizedNativeCoefficient17)
    (oddIReal17 normalizedNativeCoefficient17)
    (oddJReal17 normalizedNativeCoefficient17)
    (oddKReal17 normalizedNativeCoefficient17)).symm

private theorem native_odd_fourth_block_normalized_scale17 :
    oddFourthB (fun j => C3CofactorCorrelation.nativeC j.val) =
      (C3CofactorCorrelation.nativeC 0 ^ 2) •
        oddFourthB normalizedNativeCoefficient17 := by
  have h0 := native_c0_gt_49_100
  have h0pos : 0 < C3CofactorCorrelation.nativeC 0 :=
    lt_trans (by norm_num : (0 : ℝ) < 49/100) h0
  have hcoeff (j : Fin 9) : C3CofactorCorrelation.nativeC j.val =
      C3CofactorCorrelation.nativeC 0 * normalizedNativeCoefficient17 j := by
    unfold normalizedNativeCoefficient17
    field_simp [ne_of_gt h0pos]
  have hnorm0 : normalizedNativeCoefficient17 (0 : Fin 9) = 1 := by
    simp [normalizedNativeCoefficient17, ne_of_gt h0pos]
  have hc1 : C3CofactorCorrelation.nativeC 1 =
      C3CofactorCorrelation.nativeC 0 * normalizedNativeCoefficient17 (1 : Fin 9) := by
    simpa using hcoeff (1 : Fin 9)
  have hc2 : C3CofactorCorrelation.nativeC 2 =
      C3CofactorCorrelation.nativeC 0 * normalizedNativeCoefficient17 (2 : Fin 9) := by
    simpa using hcoeff (2 : Fin 9)
  have hc3 : C3CofactorCorrelation.nativeC 3 =
      C3CofactorCorrelation.nativeC 0 * normalizedNativeCoefficient17 (3 : Fin 9) := by
    simpa using hcoeff (3 : Fin 9)
  have hc4 : C3CofactorCorrelation.nativeC 4 =
      C3CofactorCorrelation.nativeC 0 * normalizedNativeCoefficient17 (4 : Fin 9) := by
    simpa using hcoeff (4 : Fin 9)
  have hc5 : C3CofactorCorrelation.nativeC 5 =
      C3CofactorCorrelation.nativeC 0 * normalizedNativeCoefficient17 (5 : Fin 9) := by
    simpa using hcoeff (5 : Fin 9)
  have hc6 : C3CofactorCorrelation.nativeC 6 =
      C3CofactorCorrelation.nativeC 0 * normalizedNativeCoefficient17 (6 : Fin 9) := by
    simpa using hcoeff (6 : Fin 9)
  have hc7 : C3CofactorCorrelation.nativeC 7 =
      C3CofactorCorrelation.nativeC 0 * normalizedNativeCoefficient17 (7 : Fin 9) := by
    simpa using hcoeff (7 : Fin 9)
  have hc8 : C3CofactorCorrelation.nativeC 8 =
      C3CofactorCorrelation.nativeC 0 * normalizedNativeCoefficient17 (8 : Fin 9) := by
    simpa using hcoeff (8 : Fin 9)
  ext x y
  fin_cases x <;> fin_cases y <;>
    simp [oddFourthB, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hnorm0] <;> ring

private theorem RationalBall.refine_contains {a b : RationalBall} {x : ℝ}
    (hbound : |a.center - b.center| + a.radius ≤ b.radius)
    (ha : a.Contains x) : b.Contains x := by
  change |x - (b.center : ℝ)| ≤ (b.radius : ℝ)
  have htri : |x - (b.center : ℝ)| ≤
      |x - (a.center : ℝ)| + |(a.center : ℝ) - (b.center : ℝ)| := by
    have heq : x - (b.center : ℝ) =
        (x - (a.center : ℝ)) + ((a.center : ℝ) - (b.center : ℝ)) := by ring
    rw [heq]
    exact abs_add_le _ _
  have hboundR :
      |(a.center : ℝ) - (b.center : ℝ)| + (a.radius : ℝ) ≤ (b.radius : ℝ) := by
    exact_mod_cast hbound
  calc
    |x - (b.center : ℝ)| ≤ |x - (a.center : ℝ)| + |(a.center : ℝ) - (b.center : ℝ)| := htri
    _ ≤ (a.radius : ℝ) + |(a.center : ℝ) - (b.center : ℝ)| := add_le_add ha le_rfl
    _ = |(a.center : ℝ) - (b.center : ℝ)| + (a.radius : ℝ) := add_comm _ _
    _ ≤ (b.radius : ℝ) := hboundR

private def roundedBall17 (centerUnits radiusUnits : Int) : RationalBall :=
  ⟨(centerUnits : ℚ) / 10^80, (radiusUnits : ℚ) / 10^80⟩

private def oddACoarseBall17 := roundedBall17 3717259928526968616486626247174057845337449997960376792753929581048161769114 204620998623083794157886762086067802800676375466176000000001
private def oddBCoarseBall17 := roundedBall17 (-71469871916741097331133403135093216617099512393017904128506038710039353154) 32335332716920811496565766687554783172958349470010000000001
private def oddECoarseBall17 := roundedBall17 656311625820108085827638397266499528085215573430392199039458178465748584 4231217366416988202885436967247631222810954478130800000001
private def oddHCoarseBall17 := roundedBall17 (-3854242072373451218111759684267558885469309302740636929095904520829538) 523105796185161075161104935089329789009656003192880000001
private def oddDCoarseBall17 := roundedBall17 1384500297377240322938313263495144582567696996148951850671410451807879425 4561768354349634076260416512578789536102555903949600000001
private def oddFCoarseBall17 := roundedBall17 (-12794313738284203376149277879735953888641881108997445379894974383013633) 574618940156863098989989660060647887107271766607040000001
private def oddICoarseBall17 := roundedBall17 75540295593282357943567284941756943777571015196168992638460664373548 609740283253773117531229938817585329937595959266792000001
private def oddGCoarseBall17 := roundedBall17 118859054316590522766494684248554325921516059876689073647545672116575 609840744411452214525889256584129979603877382159992000001
private def oddJCoarseBall17 := roundedBall17 (-704935234962555479894216662480831968838898353206018816824825650297) 81632269616053061965793975654109737559897790838466000001
private def oddKCoarseBall17 := roundedBall17 4196986307871998105044765268977789445367119110293687755609759068 801486032947091723365917341340800183492707643891744800001

private theorem oddABall17_refines :
    |oddABall17.center - oddACoarseBall17.center| + oddABall17.radius ≤
      oddACoarseBall17.radius := by
  norm_num [oddABall17, oddACoarseBall17, roundedBall17, normCoeffBall17,
    normalizedCoefficientCandidate17, rbSub, rbMul, rbScale, RationalBall.sub,
    RationalBall.add, RationalBall.neg, RationalBall.mul, RationalBall.point]
private theorem oddBBall17_refines :
    |oddBBall17.center - oddBCoarseBall17.center| + oddBBall17.radius ≤
      oddBCoarseBall17.radius := by
  norm_num [oddBBall17, oddBCoarseBall17, roundedBall17, normCoeffBall17,
    normalizedCoefficientCandidate17, rbSub, rbMul, rbScale, RationalBall.sub,
    RationalBall.add, RationalBall.neg, RationalBall.mul, RationalBall.point]
private theorem oddEBall17_refines :
    |oddEBall17.center - oddECoarseBall17.center| + oddEBall17.radius ≤
      oddECoarseBall17.radius := by
  norm_num [oddEBall17, oddECoarseBall17, roundedBall17, normCoeffBall17,
    normalizedCoefficientCandidate17, rbSub, rbMul, rbScale, RationalBall.sub,
    RationalBall.add, RationalBall.neg, RationalBall.mul, RationalBall.point]
private theorem oddHBall17_refines :
    |oddHBall17.center - oddHCoarseBall17.center| + oddHBall17.radius ≤
      oddHCoarseBall17.radius := by
  norm_num [oddHBall17, oddHCoarseBall17, roundedBall17, normCoeffBall17,
    normalizedCoefficientCandidate17, rbSub, rbMul, rbScale, RationalBall.sub,
    RationalBall.add, RationalBall.neg, RationalBall.mul, RationalBall.point]
private theorem oddDBall17_refines :
    |oddDBall17.center - oddDCoarseBall17.center| + oddDBall17.radius ≤
      oddDCoarseBall17.radius := by
  norm_num [oddDBall17, oddDCoarseBall17, roundedBall17, normCoeffBall17,
    normalizedCoefficientCandidate17, rbSub, rbMul, rbScale, RationalBall.sub,
    RationalBall.add, RationalBall.neg, RationalBall.mul, RationalBall.point]
private theorem oddFBall17_refines :
    |oddFBall17.center - oddFCoarseBall17.center| + oddFBall17.radius ≤
      oddFCoarseBall17.radius := by
  norm_num [oddFBall17, oddFCoarseBall17, roundedBall17, normCoeffBall17,
    normalizedCoefficientCandidate17, rbSub, rbMul, rbScale, RationalBall.sub,
    RationalBall.add, RationalBall.neg, RationalBall.mul, RationalBall.point]
private theorem oddIBall17_refines :
    |oddIBall17.center - oddICoarseBall17.center| + oddIBall17.radius ≤
      oddICoarseBall17.radius := by
  norm_num [oddIBall17, oddICoarseBall17, roundedBall17, normCoeffBall17,
    normalizedCoefficientCandidate17, rbSub, rbMul, rbScale, RationalBall.sub,
    RationalBall.add, RationalBall.neg, RationalBall.mul, RationalBall.point]
private theorem oddGBall17_refines :
    |oddGBall17.center - oddGCoarseBall17.center| + oddGBall17.radius ≤
      oddGCoarseBall17.radius := by
  norm_num [oddGBall17, oddGCoarseBall17, roundedBall17, normCoeffBall17,
    normalizedCoefficientCandidate17, rbSub, rbMul, rbScale, RationalBall.sub,
    RationalBall.add, RationalBall.neg, RationalBall.mul, RationalBall.point]
private theorem oddJBall17_refines :
    |oddJBall17.center - oddJCoarseBall17.center| + oddJBall17.radius ≤
      oddJCoarseBall17.radius := by
  norm_num [oddJBall17, oddJCoarseBall17, roundedBall17, normCoeffBall17,
    normalizedCoefficientCandidate17, rbSub, rbMul, rbScale, RationalBall.sub,
    RationalBall.add, RationalBall.neg, RationalBall.mul, RationalBall.point]
private theorem oddKBall17_refines :
    |oddKBall17.center - oddKCoarseBall17.center| + oddKBall17.radius ≤
      oddKCoarseBall17.radius := by
  norm_num [oddKBall17, oddKCoarseBall17, roundedBall17, normCoeffBall17,
    normalizedCoefficientCandidate17, rbSub, rbMul, rbScale, RationalBall.sub,
    RationalBall.add, RationalBall.neg, RationalBall.mul, RationalBall.point]

private theorem odd_coarse_component_balls17_contains (c : Fin 9 → ℝ)
    (hc : ∀ j, (normCoeffBall17 j).Contains (c j)) :
    oddACoarseBall17.Contains (oddAReal17 c) ∧
    oddBCoarseBall17.Contains (oddBReal17 c) ∧
    oddECoarseBall17.Contains (oddEReal17 c) ∧
    oddHCoarseBall17.Contains (oddHReal17 c) ∧
    oddDCoarseBall17.Contains (oddDReal17 c) ∧
    oddFCoarseBall17.Contains (oddFReal17 c) ∧
    oddICoarseBall17.Contains (oddIReal17 c) ∧
    oddGCoarseBall17.Contains (oddGReal17 c) ∧
    oddJCoarseBall17.Contains (oddJReal17 c) ∧
    oddKCoarseBall17.Contains (oddKReal17 c) := by
  rcases odd_component_balls17_contains c hc with
    ⟨ha, hb, he, hh, hd, hf, hi, hg, hj, hk⟩
  exact ⟨RationalBall.refine_contains oddABall17_refines ha,
    RationalBall.refine_contains oddBBall17_refines hb,
    RationalBall.refine_contains oddEBall17_refines he,
    RationalBall.refine_contains oddHBall17_refines hh,
    RationalBall.refine_contains oddDBall17_refines hd,
    RationalBall.refine_contains oddFBall17_refines hf,
    RationalBall.refine_contains oddIBall17_refines hi,
    RationalBall.refine_contains oddGBall17_refines hg,
    RationalBall.refine_contains oddJBall17_refines hj,
    RationalBall.refine_contains oddKBall17_refines hk⟩

private def detACalcCoarse17 :=
  rbSub (rbSub (rbSub
    (rbAdd (rbMul (rbMul oddACoarseBall17 oddDCoarseBall17) oddGCoarseBall17)
      (rbScale 2 (rbMul (rbMul oddBCoarseBall17 oddECoarseBall17) oddFCoarseBall17)))
    (rbMul oddACoarseBall17 (rbMul oddFCoarseBall17 oddFCoarseBall17)))
    (rbMul oddDCoarseBall17 (rbMul oddECoarseBall17 oddECoarseBall17)))
    (rbMul oddGCoarseBall17 (rbMul oddBCoarseBall17 oddBCoarseBall17))
private def detACoarseBall17 := roundedBall17
  31199602899961529524292972559926342947001792967397
  638273779181948527898049188899043034025676846

private def energyCalcCoarse17 :=
  rbAdd (rbAdd (rbAdd (rbAdd (rbAdd (rbAdd (rbAdd (rbAdd (rbAdd
    (rbMul oddACoarseBall17 (rbMul u0Ball17 u0Ball17))
    (rbMul (rbScale 2 oddBCoarseBall17) (rbMul u0Ball17 u1Ball17)))
    (rbMul (rbScale 2 oddECoarseBall17) (rbMul u0Ball17 u2Ball17)))
    (rbMul oddDCoarseBall17 (rbMul u1Ball17 u1Ball17)))
    (rbMul (rbScale 2 oddFCoarseBall17) (rbMul u1Ball17 u2Ball17)))
    (rbMul oddGCoarseBall17 (rbMul u2Ball17 u2Ball17)))
    (rbMul (rbScale 2 oddHCoarseBall17) u0Ball17))
    (rbMul (rbScale 2 oddICoarseBall17) u1Ball17))
    (rbMul (rbScale 2 oddJCoarseBall17) u2Ball17))
    oddKCoarseBall17
private def energyCoarseBall17 := roundedBall17
  2962261727717689677939830246111426334651841309787313896709
  804322806183711966188500279326632999169504623605036881320

private def r0CalcCoarse17 :=
  rbAdd (rbAdd (rbAdd (rbMul oddACoarseBall17 u0Ball17)
    (rbMul oddBCoarseBall17 u1Ball17)) (rbMul oddECoarseBall17 u2Ball17)) oddHCoarseBall17
private def r1CalcCoarse17 :=
  rbAdd (rbAdd (rbAdd (rbMul oddBCoarseBall17 u0Ball17)
    (rbMul oddDCoarseBall17 u1Ball17)) (rbMul oddFCoarseBall17 u2Ball17)) oddICoarseBall17
private def r2CalcCoarse17 :=
  rbAdd (rbAdd (rbAdd (rbMul oddECoarseBall17 u0Ball17)
    (rbMul oddFCoarseBall17 u1Ball17)) (rbMul oddGCoarseBall17 u2Ball17)) oddJCoarseBall17
private def r0CoarseBall17 := roundedBall17
  (-212820791951930803300462239253301027517703791851864315)
  592965465134752566371598159616233574647635719673584787682
private def r1CoarseBall17 := roundedBall17
  4091823177185904691331939591869528252052195422454774
  619251883485750539622444815224540025781456912089785859235
private def r2CoarseBall17 := roundedBall17
  (-37575628938406541567511645667375588674948834939919)
  91175419046777642090262634480664886840407577226029915471

private def adjQuadCalcCoarse17 :=
  rbAdd (rbAdd (rbAdd (rbAdd (rbAdd
    (rbMul (rbSub (rbMul oddDCoarseBall17 oddGCoarseBall17)
      (rbMul oddFCoarseBall17 oddFCoarseBall17)) (rbMul r0CoarseBall17 r0CoarseBall17))
    (rbMul (rbSub (rbMul oddACoarseBall17 oddGCoarseBall17)
      (rbMul oddECoarseBall17 oddECoarseBall17)) (rbMul r1CoarseBall17 r1CoarseBall17)))
    (rbMul (rbSub (rbMul oddACoarseBall17 oddDCoarseBall17)
      (rbMul oddBCoarseBall17 oddBCoarseBall17)) (rbMul r2CoarseBall17 r2CoarseBall17)))
    (rbMul (rbScale 2 (rbSub (rbMul oddECoarseBall17 oddFCoarseBall17)
      (rbMul oddBCoarseBall17 oddGCoarseBall17))) (rbMul r0CoarseBall17 r1CoarseBall17)))
    (rbMul (rbScale 2 (rbSub (rbMul oddBCoarseBall17 oddFCoarseBall17)
      (rbMul oddDCoarseBall17 oddECoarseBall17))) (rbMul r0CoarseBall17 r2CoarseBall17)))
    (rbMul (rbScale 2 (rbSub (rbMul oddBCoarseBall17 oddECoarseBall17)
      (rbMul oddACoarseBall17 oddFCoarseBall17))) (rbMul r1CoarseBall17 r2CoarseBall17))
private def adjQuadCoarseBall17 := roundedBall17 4 399635204175262895

private def cofactorGateCalcCoarse17 :=
  rbSub (rbMul detACoarseBall17 energyCoarseBall17) adjQuadCoarseBall17
private def cofactorGateBall17 := roundedBall17
  924213895905458816393175729 250969563084231170553617677

private theorem detACalcCoarse17_refines :
    |detACalcCoarse17.center - detACoarseBall17.center| +
      detACalcCoarse17.radius ≤ detACoarseBall17.radius := by
  norm_num [detACalcCoarse17, detACoarseBall17, roundedBall17, oddACoarseBall17,
    oddBCoarseBall17, oddECoarseBall17, oddDCoarseBall17, oddFCoarseBall17,
    oddGCoarseBall17, rbAdd, rbSub, rbMul, rbScale, RationalBall.sub,
    RationalBall.add, RationalBall.neg, RationalBall.mul, RationalBall.point]
private theorem energyCalcCoarse17_refines :
    |energyCalcCoarse17.center - energyCoarseBall17.center| +
      energyCalcCoarse17.radius ≤ energyCoarseBall17.radius := by
  norm_num [energyCalcCoarse17, energyCoarseBall17, roundedBall17, oddACoarseBall17,
    oddBCoarseBall17, oddECoarseBall17, oddHCoarseBall17, oddDCoarseBall17,
    oddFCoarseBall17, oddGCoarseBall17, oddICoarseBall17, oddJCoarseBall17,
    oddKCoarseBall17, u0Ball17, u1Ball17, u2Ball17, rbAdd, rbSub, rbMul, rbScale, RationalBall.sub,
    RationalBall.add, RationalBall.neg, RationalBall.mul, RationalBall.point]
private theorem r0CalcCoarse17_refines :
    |r0CalcCoarse17.center - r0CoarseBall17.center| + r0CalcCoarse17.radius ≤
      r0CoarseBall17.radius := by
  norm_num [r0CalcCoarse17, r0CoarseBall17, roundedBall17, oddACoarseBall17,
    oddBCoarseBall17, oddECoarseBall17, oddHCoarseBall17, u0Ball17, u1Ball17,
    u2Ball17, rbAdd, rbSub, rbMul, rbScale, RationalBall.sub, RationalBall.add,
    RationalBall.neg, RationalBall.mul, RationalBall.point]
private theorem r1CalcCoarse17_refines :
    |r1CalcCoarse17.center - r1CoarseBall17.center| + r1CalcCoarse17.radius ≤
      r1CoarseBall17.radius := by
  norm_num [r1CalcCoarse17, r1CoarseBall17, roundedBall17, oddBCoarseBall17,
    oddDCoarseBall17, oddFCoarseBall17, oddICoarseBall17, u0Ball17, u1Ball17,
    u2Ball17, rbAdd, rbSub, rbMul, rbScale, RationalBall.sub, RationalBall.add,
    RationalBall.neg, RationalBall.mul, RationalBall.point]
private theorem r2CalcCoarse17_refines :
    |r2CalcCoarse17.center - r2CoarseBall17.center| + r2CalcCoarse17.radius ≤
      r2CoarseBall17.radius := by
  norm_num [r2CalcCoarse17, r2CoarseBall17, roundedBall17, oddECoarseBall17,
    oddFCoarseBall17, oddGCoarseBall17, oddJCoarseBall17, u0Ball17, u1Ball17,
    u2Ball17, rbAdd, rbSub, rbMul, rbScale, RationalBall.sub, RationalBall.add,
    RationalBall.neg, RationalBall.mul, RationalBall.point]
private theorem adjQuadCalcCoarse17_refines :
    |adjQuadCalcCoarse17.center - adjQuadCoarseBall17.center| +
      adjQuadCalcCoarse17.radius ≤ adjQuadCoarseBall17.radius := by
  norm_num [adjQuadCalcCoarse17, adjQuadCoarseBall17, roundedBall17,
    oddACoarseBall17, oddBCoarseBall17, oddECoarseBall17, oddDCoarseBall17,
    oddFCoarseBall17, oddGCoarseBall17, r0CoarseBall17, r1CoarseBall17,
    r2CoarseBall17, rbAdd, rbSub, rbMul, rbScale, RationalBall.sub,
    RationalBall.add, RationalBall.neg, RationalBall.mul, RationalBall.point]
private theorem cofactorGateCalcCoarse17_refines :
    |cofactorGateCalcCoarse17.center - cofactorGateBall17.center| +
      cofactorGateCalcCoarse17.radius ≤ cofactorGateBall17.radius := by
  norm_num [cofactorGateCalcCoarse17, cofactorGateBall17, detACoarseBall17,
    energyCoarseBall17, adjQuadCoarseBall17, roundedBall17, rbAdd, rbSub,
    rbMul, rbScale, RationalBall.sub, RationalBall.add, RationalBall.neg,
    RationalBall.mul, RationalBall.point]


private theorem detACalcCoarse17_contains (c : Fin 9 → ℝ)
    (ha : oddACoarseBall17.Contains (oddAReal17 c))
    (hb : oddBCoarseBall17.Contains (oddBReal17 c))
    (he : oddECoarseBall17.Contains (oddEReal17 c))
    (hd : oddDCoarseBall17.Contains (oddDReal17 c))
    (hf : oddFCoarseBall17.Contains (oddFReal17 c))
    (hg : oddGCoarseBall17.Contains (oddGReal17 c)) :
    detACalcCoarse17.Contains
      (detAReal17 (oddAReal17 c) (oddBReal17 c) (oddEReal17 c)
        (oddDReal17 c) (oddFReal17 c) (oddGReal17 c)) := by
  dsimp [detACalcCoarse17, detAReal17, rbAdd, rbSub, rbMul, rbScale]
  repeat first
    | assumption
    | exact RationalBall.point_contains _
    | apply RationalBall.add_contains
    | apply RationalBall.sub_contains
    | apply RationalBall.neg_contains
    | apply RationalBall.mul_contains

private theorem energyCalcCoarse17_contains (c : Fin 9 → ℝ)
    (ha : oddACoarseBall17.Contains (oddAReal17 c))
    (hb : oddBCoarseBall17.Contains (oddBReal17 c))
    (he : oddECoarseBall17.Contains (oddEReal17 c))
    (hh : oddHCoarseBall17.Contains (oddHReal17 c))
    (hd : oddDCoarseBall17.Contains (oddDReal17 c))
    (hf : oddFCoarseBall17.Contains (oddFReal17 c))
    (hi : oddICoarseBall17.Contains (oddIReal17 c))
    (hg : oddGCoarseBall17.Contains (oddGReal17 c))
    (hj : oddJCoarseBall17.Contains (oddJReal17 c))
    (hk : oddKCoarseBall17.Contains (oddKReal17 c)) :
    energyCalcCoarse17.Contains
      (energyReal17 (oddAReal17 c) (oddBReal17 c) (oddEReal17 c)
        (oddDReal17 c) (oddFReal17 c) (oddGReal17 c) (oddHReal17 c)
        (oddIReal17 c) (oddJReal17 c) (oddKReal17 c)) := by
  have hu0 : u0Ball17.Contains u0Real17 := by
    norm_num [u0Ball17, u0Real17, RationalBall.point, RationalBall.Contains]
  have hu1 : u1Ball17.Contains u1Real17 := by
    norm_num [u1Ball17, u1Real17, RationalBall.point, RationalBall.Contains]
  have hu2 : u2Ball17.Contains u2Real17 := by
    norm_num [u2Ball17, u2Real17, RationalBall.point, RationalBall.Contains]
  dsimp [energyCalcCoarse17, energyReal17, rbAdd, rbSub, rbMul, rbScale]
  repeat first
    | assumption
    | exact RationalBall.point_contains _
    | apply RationalBall.add_contains
    | apply RationalBall.sub_contains
    | apply RationalBall.neg_contains
    | apply RationalBall.mul_contains

private theorem r0CalcCoarse17_contains (c : Fin 9 → ℝ)
    (ha : oddACoarseBall17.Contains (oddAReal17 c))
    (hb : oddBCoarseBall17.Contains (oddBReal17 c))
    (he : oddECoarseBall17.Contains (oddEReal17 c))
    (hh : oddHCoarseBall17.Contains (oddHReal17 c)) :
    r0CalcCoarse17.Contains
      (r0Real17 (oddAReal17 c) (oddBReal17 c) (oddEReal17 c)
        (oddHReal17 c)) := by
  have hu0 : u0Ball17.Contains u0Real17 := by
    norm_num [u0Ball17, u0Real17, RationalBall.point, RationalBall.Contains]
  have hu1 : u1Ball17.Contains u1Real17 := by
    norm_num [u1Ball17, u1Real17, RationalBall.point, RationalBall.Contains]
  have hu2 : u2Ball17.Contains u2Real17 := by
    norm_num [u2Ball17, u2Real17, RationalBall.point, RationalBall.Contains]
  dsimp [r0CalcCoarse17, r0Real17, rbAdd, rbSub, rbMul, rbScale]
  repeat first
    | assumption
    | exact RationalBall.point_contains _
    | apply RationalBall.add_contains
    | apply RationalBall.sub_contains
    | apply RationalBall.neg_contains
    | apply RationalBall.mul_contains

private theorem r1CalcCoarse17_contains (c : Fin 9 → ℝ)
    (hb : oddBCoarseBall17.Contains (oddBReal17 c))
    (hd : oddDCoarseBall17.Contains (oddDReal17 c))
    (hf : oddFCoarseBall17.Contains (oddFReal17 c))
    (hi : oddICoarseBall17.Contains (oddIReal17 c)) :
    r1CalcCoarse17.Contains
      (r1Real17 (oddBReal17 c) (oddDReal17 c) (oddFReal17 c)
        (oddIReal17 c)) := by
  have hu0 : u0Ball17.Contains u0Real17 := by
    norm_num [u0Ball17, u0Real17, RationalBall.point, RationalBall.Contains]
  have hu1 : u1Ball17.Contains u1Real17 := by
    norm_num [u1Ball17, u1Real17, RationalBall.point, RationalBall.Contains]
  have hu2 : u2Ball17.Contains u2Real17 := by
    norm_num [u2Ball17, u2Real17, RationalBall.point, RationalBall.Contains]
  dsimp [r1CalcCoarse17, r1Real17, rbAdd, rbSub, rbMul, rbScale]
  repeat first
    | assumption
    | exact RationalBall.point_contains _
    | apply RationalBall.add_contains
    | apply RationalBall.sub_contains
    | apply RationalBall.neg_contains
    | apply RationalBall.mul_contains

private theorem r2CalcCoarse17_contains (c : Fin 9 → ℝ)
    (he : oddECoarseBall17.Contains (oddEReal17 c))
    (hf : oddFCoarseBall17.Contains (oddFReal17 c))
    (hg : oddGCoarseBall17.Contains (oddGReal17 c))
    (hj : oddJCoarseBall17.Contains (oddJReal17 c)) :
    r2CalcCoarse17.Contains
      (r2Real17 (oddEReal17 c) (oddFReal17 c) (oddGReal17 c)
        (oddJReal17 c)) := by
  have hu0 : u0Ball17.Contains u0Real17 := by
    norm_num [u0Ball17, u0Real17, RationalBall.point, RationalBall.Contains]
  have hu1 : u1Ball17.Contains u1Real17 := by
    norm_num [u1Ball17, u1Real17, RationalBall.point, RationalBall.Contains]
  have hu2 : u2Ball17.Contains u2Real17 := by
    norm_num [u2Ball17, u2Real17, RationalBall.point, RationalBall.Contains]
  dsimp [r2CalcCoarse17, r2Real17, rbAdd, rbSub, rbMul, rbScale]
  repeat first
    | assumption
    | exact RationalBall.point_contains _
    | apply RationalBall.add_contains
    | apply RationalBall.sub_contains
    | apply RationalBall.neg_contains
    | apply RationalBall.mul_contains

private theorem adjQuadCalcCoarse17_contains (c : Fin 9 → ℝ)
    (ha : oddACoarseBall17.Contains (oddAReal17 c))
    (hb : oddBCoarseBall17.Contains (oddBReal17 c))
    (he : oddECoarseBall17.Contains (oddEReal17 c))
    (hd : oddDCoarseBall17.Contains (oddDReal17 c))
    (hf : oddFCoarseBall17.Contains (oddFReal17 c))
    (hg : oddGCoarseBall17.Contains (oddGReal17 c))
    (hr0 : r0CoarseBall17.Contains
      (r0Real17 (oddAReal17 c) (oddBReal17 c) (oddEReal17 c) (oddHReal17 c)))
    (hr1 : r1CoarseBall17.Contains
      (r1Real17 (oddBReal17 c) (oddDReal17 c) (oddFReal17 c) (oddIReal17 c)))
    (hr2 : r2CoarseBall17.Contains
      (r2Real17 (oddEReal17 c) (oddFReal17 c) (oddGReal17 c) (oddJReal17 c))) :
    adjQuadCalcCoarse17.Contains
      (adjQuadReal17 (oddAReal17 c) (oddBReal17 c) (oddEReal17 c)
        (oddDReal17 c) (oddFReal17 c) (oddGReal17 c)
        (r0Real17 (oddAReal17 c) (oddBReal17 c) (oddEReal17 c) (oddHReal17 c))
        (r1Real17 (oddBReal17 c) (oddDReal17 c) (oddFReal17 c) (oddIReal17 c))
        (r2Real17 (oddEReal17 c) (oddFReal17 c) (oddGReal17 c) (oddJReal17 c))) := by
  dsimp [adjQuadCalcCoarse17, adjQuadReal17, rbAdd, rbSub, rbMul, rbScale]
  repeat first
    | assumption
    | exact RationalBall.point_contains _
    | apply RationalBall.add_contains
    | apply RationalBall.sub_contains
    | apply RationalBall.neg_contains
    | apply RationalBall.mul_contains

private theorem cofactorGateCalcCoarse17_contains (c : Fin 9 → ℝ)
    (hdet : detACoarseBall17.Contains
      (detAReal17 (oddAReal17 c) (oddBReal17 c) (oddEReal17 c)
        (oddDReal17 c) (oddFReal17 c) (oddGReal17 c)))
    (henergy : energyCoarseBall17.Contains
      (energyReal17 (oddAReal17 c) (oddBReal17 c) (oddEReal17 c)
        (oddDReal17 c) (oddFReal17 c) (oddGReal17 c) (oddHReal17 c)
        (oddIReal17 c) (oddJReal17 c) (oddKReal17 c)))
    (hadj : adjQuadCoarseBall17.Contains
      (adjQuadReal17 (oddAReal17 c) (oddBReal17 c) (oddEReal17 c)
        (oddDReal17 c) (oddFReal17 c) (oddGReal17 c)
        (r0Real17 (oddAReal17 c) (oddBReal17 c) (oddEReal17 c) (oddHReal17 c))
        (r1Real17 (oddBReal17 c) (oddDReal17 c) (oddFReal17 c) (oddIReal17 c))
        (r2Real17 (oddEReal17 c) (oddFReal17 c) (oddGReal17 c) (oddJReal17 c)))) :
    cofactorGateCalcCoarse17.Contains
      (cofactorGateReal17 (oddAReal17 c) (oddBReal17 c) (oddEReal17 c)
        (oddDReal17 c) (oddFReal17 c) (oddGReal17 c) (oddHReal17 c)
        (oddIReal17 c) (oddJReal17 c) (oddKReal17 c)) := by
  simpa [cofactorGateCalcCoarse17, cofactorGateReal17, rbSub, rbMul,
    RationalBall.sub] using
    RationalBall.sub_contains (RationalBall.mul_contains hdet henergy) hadj

private theorem cofactor_gate_stage_ball17_contains (c : Fin 9 → ℝ)
    (hc : ∀ j, (normCoeffBall17 j).Contains (c j)) :
    cofactorGateBall17.Contains
      (cofactorGateReal17 (oddAReal17 c) (oddBReal17 c) (oddEReal17 c)
        (oddDReal17 c) (oddFReal17 c) (oddGReal17 c)
        (oddHReal17 c) (oddIReal17 c) (oddJReal17 c) (oddKReal17 c)) := by
  rcases odd_coarse_component_balls17_contains c hc with
    ⟨ha, hb, he, hh, hd, hf, hi, hg, hj, hk⟩
  have hdetCalc := detACalcCoarse17_contains c ha hb he hd hf hg
  have henergyCalc := energyCalcCoarse17_contains c ha hb he hh hd hf hi hg hj hk
  have hr0Calc := r0CalcCoarse17_contains c ha hb he hh
  have hr1Calc := r1CalcCoarse17_contains c hb hd hf hi
  have hr2Calc := r2CalcCoarse17_contains c he hf hg hj
  have hdet := RationalBall.refine_contains detACalcCoarse17_refines hdetCalc
  have henergy := RationalBall.refine_contains energyCalcCoarse17_refines henergyCalc
  have hr0 := RationalBall.refine_contains r0CalcCoarse17_refines hr0Calc
  have hr1 := RationalBall.refine_contains r1CalcCoarse17_refines hr1Calc
  have hr2 := RationalBall.refine_contains r2CalcCoarse17_refines hr2Calc
  have hadjCalc := adjQuadCalcCoarse17_contains c ha hb he hd hf hg hr0 hr1 hr2
  have hadj := RationalBall.refine_contains adjQuadCalcCoarse17_refines hadjCalc
  have hgateCalc := cofactorGateCalcCoarse17_contains c hdet henergy hadj
  exact RationalBall.refine_contains cofactorGateCalcCoarse17_refines hgateCalc

private theorem cofactor_gate_lower_bound17 :
    (67 / 10^55 : ℚ) < cofactorGateBall17.center - cofactorGateBall17.radius := by
  decide +kernel

theorem native_normalized_fourth_cofactor_gate17 :
    0 < cofactorGateReal17
      (oddAReal17 normalizedNativeCoefficient17)
      (oddBReal17 normalizedNativeCoefficient17)
      (oddEReal17 normalizedNativeCoefficient17)
      (oddDReal17 normalizedNativeCoefficient17)
      (oddFReal17 normalizedNativeCoefficient17)
      (oddGReal17 normalizedNativeCoefficient17)
      (oddHReal17 normalizedNativeCoefficient17)
      (oddIReal17 normalizedNativeCoefficient17)
      (oddJReal17 normalizedNativeCoefficient17)
      (oddKReal17 normalizedNativeCoefficient17) := by
  have hbox := cofactor_gate_stage_ball17_contains normalizedNativeCoefficient17
    normalized_native_coefficient17_contains
  have hlower := RationalBall.lower_le_of_contains hbox
  have hpositive : (0:ℚ) < cofactorGateBall17.center - cofactorGateBall17.radius :=
    lt_trans (by norm_num : (0:ℚ) < 67/10^55) cofactor_gate_lower_bound17
  exact lt_of_lt_of_le (by exact_mod_cast hpositive) hlower

theorem native_odd_fourth_bezout_determinant_positive17 :
    0 < (coefficientBlock
      (sourceKernel C3CofactorCorrelation.nativeC true) 4).det := by
  rw [native_odd_fourth_block_eq, native_odd_fourth_block_normalized_scale17,
    Matrix.det_smul]
  have hcard : Fintype.card (Fin 4) = 4 := rfl
  rw [hcard]
  have h0 := native_c0_gt_49_100
  have h0pos : 0 < C3CofactorCorrelation.nativeC 0 :=
    lt_trans (by norm_num : (0 : ℝ) < 49/100) h0
  have hscale : 0 < (C3CofactorCorrelation.nativeC 0 ^ 2) ^ 4 :=
    pow_pos (pow_pos h0pos 2) 4
  have hdet : 0 < (oddFourthB normalizedNativeCoefficient17).det := by
    rw [native_normalized_fourth_determinant_eq_gate17]
    exact native_normalized_fourth_cofactor_gate17
  exact mul_pos hscale hdet

private theorem native_odd_fourth_is_border17 :
    coefficientBlock (sourceKernel C3CofactorCorrelation.nativeC true) 4 =
      C3GeneralCofactor.border
        (coefficientBlock (sourceKernel C3CofactorCorrelation.nativeC true) 3)
        (sourceCoupling C3CofactorCorrelation.nativeC true 3)
        (coefficientBlock (sourceKernel C3CofactorCorrelation.nativeC true) 4
          (Fin.last 3) (Fin.last 3)) := by
  let B := coefficientBlock (sourceKernel C3CofactorCorrelation.nativeC true) 4
  have hsymmetric : B.transpose = B := by
    dsimp [B]
    exact source_block_transpose C3CofactorCorrelation.nativeC
      nativeH native_source_recurrence
      true 4
  ext i j
  cases i using Fin.lastCases with
  | last =>
    cases j using Fin.lastCases with
    | last => rw [C3GeneralCofactor.border_last_last]
    | cast j =>
      rw [C3GeneralCofactor.border_last_castSucc]
      have h := congrFun (congrFun hsymmetric j.castSucc) (Fin.last 3)
      simpa [B, sourceCoupling, coefficientBlock] using h
  | cast i =>
    cases j using Fin.lastCases with
    | last =>
      rw [C3GeneralCofactor.border_castSucc_last]
      simp [sourceCoupling, coefficientBlock]
    | cast j =>
      rw [C3GeneralCofactor.border_castSucc_castSucc]
      simp [coefficientBlock]

private theorem native_odd_fourth_det_factor_sourceSchur17 :
    (coefficientBlock (sourceKernel C3CofactorCorrelation.nativeC true) 4).det =
      (coefficientBlock (sourceKernel C3CofactorCorrelation.nativeC true) 3).det *
        sourceSchur C3CofactorCorrelation.nativeC true 3 := by
  let A := coefficientBlock (sourceKernel C3CofactorCorrelation.nativeC true) 3
  let b := sourceCoupling C3CofactorCorrelation.nativeC true 3
  let d := coefficientBlock (sourceKernel C3CofactorCorrelation.nativeC true) 4
    (Fin.last 3) (Fin.last 3)
  have hdetA := native_odd_third_det_positive17
  have hAunit : IsUnit A := by
    apply (Matrix.isUnit_iff_isUnit_det A).mpr
    exact isUnit_iff_ne_zero.mpr (ne_of_gt hdetA)
  letI := hAunit.invertible
  have hadj : A.adjugate = A.det • A⁻¹ := by
    calc
      A.adjugate = (1 : Matrix (Fin 3) (Fin 3) ℝ) * A.adjugate := by simp
      _ = (A⁻¹ * A) * A.adjugate := by rw [Matrix.inv_mul_of_invertible]
      _ = A⁻¹ * (A * A.adjugate) := by rw [Matrix.mul_assoc]
      _ = A⁻¹ * (A.det • (1 : Matrix (Fin 3) (Fin 3) ℝ)) := by
        rw [Matrix.mul_adjugate]
      _ = A.det • A⁻¹ := by rw [Matrix.mul_smul, Matrix.mul_one]
  have hterm : dotProduct b (A.adjugate.mulVec b) =
      A.det * dotProduct b (A⁻¹.mulVec b) := by
    rw [hadj, Matrix.smul_mulVec]
    simp only [dotProduct, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hterm' : (∑ i : Fin 3, b i * (A.adjugate.mulVec b) i) =
      A.det * dotProduct b (A⁻¹.mulVec b) := by
    simpa [dotProduct] using hterm
  rw [native_odd_fourth_is_border17, C3GeneralCofactor.border_det, hterm']
  change A.det * d - A.det * dotProduct b (A⁻¹.mulVec b) =
    A.det * (d - dotProduct b (A⁻¹.mulVec b))
  ring

theorem native_odd_fourth_sourceSchur_positive17 :
    0 < sourceSchur C3CofactorCorrelation.nativeC true 3 := by
  have hdetPrefix := native_odd_third_det_positive17
  have hdetFull := native_odd_fourth_bezout_determinant_positive17
  rw [native_odd_fourth_det_factor_sourceSchur17] at hdetFull
  exact (mul_pos_iff_of_pos_left hdetPrefix).mp hdetFull

theorem native_odd_fourth_momentSchur_positive17 :
    0 < CarrySelfAdjointOperator.sourceMomentSchur
      nativeH 1 3 := by
  have hB3 : (coefficientBlock (sourceKernel C3CofactorCorrelation.nativeC true) 3).PosDef := by
    rw [native_odd_third_block_eq17]
    exact C3CofactorCorrelation.completed_native_odd_third_block_posDef
  have hH3 : (sourceMomentMatrix nativeH 1 3).PosDef :=
    (native_source_bezout_posDef_iff true 3).mp hB3
  have hA : IsUnit (sourceMomentMatrix nativeH 1 3) := hH3.isUnit
  have hscale := sourceSchur_eq_scaled C3CofactorCorrelation.nativeC
    nativeH completedNativeRealEvenCharacteristicCoefficient_zero_ne_zero
    native_source_recurrence true 3 hA
  have hpivot := native_odd_fourth_sourceSchur_positive17
  rw [hscale] at hpivot
  exact (mul_pos_iff_of_pos_left
    (sq_pos_of_ne_zero
      CarrySelfAdjointOperator.completedNativeRealEvenCharacteristicCoefficient_zero_ne_zero)).mp
      hpivot

end
end C3ShiftedFourth
