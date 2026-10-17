import IntegralCertificate
import CarrySelfAdjointOperator.CompletedNativeChiralReturnEightBoundaryFace

namespace CarryReturnCompatibility
open CarryIntegralCertificate CarrySelfAdjointOperator
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 65536

def boundaryBox (n : ℕ) : Box := (Box.point 2).mul (logMomentBox n)

def eightCouplingBox0 : Box :=
  ((boundaryBox 2).mul ((boundaryBox 5).pow 2)).add
    (((Box.point 2).mul ((boundaryBox 3).mul ((boundaryBox 4).mul (boundaryBox 5)))).neg) |>.add
    ((boundaryBox 4).pow 3) |>.add
    (((boundaryBox 2).mul ((boundaryBox 4).mul (boundaryBox 6))).neg) |>.add
    (((boundaryBox 3).pow 2).mul (boundaryBox 6))

def eightCouplingBox1 : Box :=
  ((boundaryBox 1).mul ((boundaryBox 5).pow 2)).add
    (((boundaryBox 2).mul ((boundaryBox 4).mul (boundaryBox 5))).neg) |>.add
    ((boundaryBox 3).mul ((boundaryBox 4).pow 2)) |>.add
    ((((boundaryBox 3).pow 2).mul (boundaryBox 5)).neg) |>.add
    (((boundaryBox 1).mul ((boundaryBox 4).mul (boundaryBox 6))).neg) |>.add
    ((boundaryBox 2).mul ((boundaryBox 3).mul (boundaryBox 6)))

def eightCouplingBox2 : Box :=
  ((boundaryBox 1).mul ((boundaryBox 4).mul (boundaryBox 5))).add
    (((boundaryBox 2).mul ((boundaryBox 3).mul (boundaryBox 5))).neg) |>.add
    (((boundaryBox 2).mul ((boundaryBox 4).pow 2)).neg) |>.add
    (((boundaryBox 3).pow 2).mul (boundaryBox 4)) |>.add
    (((boundaryBox 1).mul ((boundaryBox 3).mul (boundaryBox 6))).neg) |>.add
    (((boundaryBox 2).pow 2).mul (boundaryBox 6))

def sixDiscriminantBox : Box :=
  ((boundaryBox 1).mul ((boundaryBox 3).mul (boundaryBox 5))).add
    (((Box.point 2).mul ((boundaryBox 2).mul ((boundaryBox 3).mul (boundaryBox 4))))) |>.add
    (((boundaryBox 3).pow 3).neg) |>.add
    (((boundaryBox 1).mul ((boundaryBox 4).pow 2)).neg) |>.add
    ((((boundaryBox 2).pow 2).mul (boundaryBox 5)).neg)

def eightDiscriminantBox : Box :=
  (sixDiscriminantBox.mul (boundaryBox 7)).add
    ((boundaryBox 4).mul eightCouplingBox0) |>.add
    (((boundaryBox 5).mul eightCouplingBox1).neg) |>.add
    ((boundaryBox 6).mul eightCouplingBox2)




theorem mem_boundaryBox (n : ℕ) :
    (boundaryBox n).Mem (nativeSourceOddBoundaryCoefficient n) := by
  rw [nativeSourceOddBoundaryCoefficient_eq_twice_primeDepthGeometricMoment,
    primeDepthGeometricMoment_eq_canonical]
  exact mem_mul (mem_point 2) (mem_logMomentBox material_theta_integral_input n)

theorem mem_eightCouplingBox0 : eightCouplingBox0.Mem nativeSourceEightOddCoupling0 := by
  unfold eightCouplingBox0 nativeSourceEightOddCoupling0
  convert (mem_add (mem_add (mem_add (mem_add (mem_mul (mem_boundaryBox 2) (mem_pow (mem_boundaryBox 5) 2)) (mem_neg (mem_mul (mem_point 2) (mem_mul (mem_boundaryBox 3) (mem_mul (mem_boundaryBox 4) (mem_boundaryBox 5)))))) (mem_pow (mem_boundaryBox 4) 3)) (mem_neg (mem_mul (mem_boundaryBox 2) (mem_mul (mem_boundaryBox 4) (mem_boundaryBox 6))))) (mem_mul (mem_pow (mem_boundaryBox 3) 2) (mem_boundaryBox 6))) using 1; ring

theorem mem_eightCouplingBox1 : eightCouplingBox1.Mem nativeSourceEightOddCoupling1 := by
  unfold eightCouplingBox1 nativeSourceEightOddCoupling1
  convert (mem_add (mem_add (mem_add (mem_add (mem_add (mem_mul (mem_boundaryBox 1) (mem_pow (mem_boundaryBox 5) 2)) (mem_neg (mem_mul (mem_boundaryBox 2) (mem_mul (mem_boundaryBox 4) (mem_boundaryBox 5))))) (mem_mul (mem_boundaryBox 3) (mem_pow (mem_boundaryBox 4) 2))) (mem_neg (mem_mul (mem_pow (mem_boundaryBox 3) 2) (mem_boundaryBox 5)))) (mem_neg (mem_mul (mem_boundaryBox 1) (mem_mul (mem_boundaryBox 4) (mem_boundaryBox 6))))) (mem_mul (mem_boundaryBox 2) (mem_mul (mem_boundaryBox 3) (mem_boundaryBox 6)))) using 1; ring

theorem mem_eightCouplingBox2 : eightCouplingBox2.Mem nativeSourceEightOddCoupling2 := by
  unfold eightCouplingBox2 nativeSourceEightOddCoupling2
  convert (mem_add (mem_add (mem_add (mem_add (mem_add (mem_mul (mem_boundaryBox 1) (mem_mul (mem_boundaryBox 4) (mem_boundaryBox 5))) (mem_neg (mem_mul (mem_boundaryBox 2) (mem_mul (mem_boundaryBox 3) (mem_boundaryBox 5))))) (mem_neg (mem_mul (mem_boundaryBox 2) (mem_pow (mem_boundaryBox 4) 2)))) (mem_mul (mem_pow (mem_boundaryBox 3) 2) (mem_boundaryBox 4))) (mem_neg (mem_mul (mem_boundaryBox 1) (mem_mul (mem_boundaryBox 3) (mem_boundaryBox 6))))) (mem_mul (mem_pow (mem_boundaryBox 2) 2) (mem_boundaryBox 6))) using 1; ring

theorem mem_sixDiscriminantBox : sixDiscriminantBox.Mem nativeSourceSixOddDiscriminant := by
  unfold sixDiscriminantBox nativeSourceSixOddDiscriminant
  convert (mem_add (mem_add (mem_add (mem_add (mem_mul (mem_boundaryBox 1) (mem_mul (mem_boundaryBox 3) (mem_boundaryBox 5))) (mem_mul (mem_point 2) (mem_mul (mem_boundaryBox 2) (mem_mul (mem_boundaryBox 3) (mem_boundaryBox 4))))) (mem_neg (mem_pow (mem_boundaryBox 3) 3))) (mem_neg (mem_mul (mem_boundaryBox 1) (mem_pow (mem_boundaryBox 4) 2)))) (mem_neg (mem_mul (mem_pow (mem_boundaryBox 2) 2) (mem_boundaryBox 5)))) using 1; ring

theorem mem_eightDiscriminantBox : eightDiscriminantBox.Mem nativeSourceEightOddDiscriminant := by
  unfold eightDiscriminantBox nativeSourceEightOddDiscriminant
  convert mem_add (mem_add (mem_add
    (mem_mul mem_sixDiscriminantBox (mem_boundaryBox 7))
    (mem_mul (mem_boundaryBox 4) mem_eightCouplingBox0))
    (mem_neg (mem_mul (mem_boundaryBox 5) mem_eightCouplingBox1)))
    (mem_mul (mem_boundaryBox 6) mem_eightCouplingBox2) using 1; ring

/-- Closed integer enclosure check, reduced by the Lean kernel. -/
theorem eighthDiscriminant_rectangle_check : eightDiscriminantBox.positive = true := by
  decide +kernel

/-- Strict sign from the UNCHANGED infinite theta source, including all
retained-mode tails and the infinite omitted-mode remainder of PR #23. -/
theorem eighthSourceDiscriminant_pos : 0 < nativeSourceEightOddDiscriminant :=
  pos_of_mem mem_eightDiscriminantBox eighthDiscriminant_rectangle_check

/-- New unconditional return bound for EIGHT actual sources. -/
theorem eighthReturn_eventually_contractive :
    ∀ᶠ k : ℕ in Filter.atTop, ‖ChiralReturn.radialReturnTransfer k 8‖ ≤ 1 :=
  radialReturnTransfer_eight_eventually_contractive_of_oddDiscriminant eighthSourceDiscriminant_pos

end CarryReturnCompatibility
