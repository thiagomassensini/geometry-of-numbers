import PhysicalPickNineEvenSignBridge
import TenSourceReturn
import CarrySelfAdjointOperator.CompletedNativeChiralReturnJordanEnergy
import Mathlib.Tactic

/-! The NINE-source C2 boundary is the ORIGINAL finite Green energy,
not a fitted Hankel or new positive norm. The fully polarized ten-source
source certificate already controls it through exact zero-padding.
In particular, every GG/GR/RG/RR cross remains in the original state. -/
namespace CarrySelfAdjointOperator
open CarrySelfAdjointOperator.ChiralReturn CarryThetaPattern Filter
open scoped BigOperators Matrix InnerProductSpace
noncomputable section
set_option autoImplicit false

theorem nativeSourceNineCompleteBoundaryEnergy_pos
    (x : Fin 9 → ℂ) (hx : x ≠ 0) :
    0 < nativeSourceFiniteBoundaryEnergy 9 x := by
  have hpad : Fin.snoc x (0 : ℂ) ≠ (0 : Fin 10 → ℂ) := by
    intro hz
    apply hx
    funext i
    have hi := congrFun hz (Fin.castSucc i)
    simpa only [Fin.snoc_castSucc, Pi.zero_apply] using hi
  have hten := CarryThetaPattern.ten_boundary_positive
    (Fin.snoc x (0 : ℂ)) hpad
  rw [nativeSourceFiniteBoundaryEnergy_snoc_zero] at hten
  exact hten

theorem nativeSourceNineReturn_eventually_contractive :
    ∀ᶠ k : ℕ in atTop,
      ‖radialReturnTransfer k 9‖ ≤ 1 :=
  CarryThetaPattern.return_contractive_through_ten 9 (by omega)

#print axioms nativeSourceNineCompleteBoundaryEnergy_pos
#print axioms nativeSourceNineReturn_eventually_contractive

end
end CarrySelfAdjointOperator
