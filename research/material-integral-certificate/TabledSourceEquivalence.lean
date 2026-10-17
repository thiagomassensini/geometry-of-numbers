import TabledSourceProgram
import QuadratureNodeChecks
import ExactSourceProof

namespace CarryIntegralCertificate
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
attribute [local irreducible] Box.Mem exactFiniteModeBox exactFullModeBox exactFullThetaMomentBox
  tabledFiniteModeBox tabledFullModeBox tabledFullThetaMomentBox

theorem exactTaylorMassBox_eq_tabled (m : Fin 3) (p j : ℕ)
    (hj : j < thetaCertificateCellCount m.val) :
    exactTaylorMassBox m.val 15 p j = tabledTaylorMassBox m.val p j := by
  unfold exactTaylorMassBox tabledTaylorMassBox
  apply Box.sum_congr
  intro r hr
  have hc := (quadrature_node_checks m ⟨j,hj⟩).1 ⟨r,hr⟩
  unfold quadratureCoefficientComputation at hc
  rw [hc]

theorem exactCellBox_eq_tabled (m : Fin 3) (p j : ℕ)
    (hj : j < thetaCertificateCellCount m.val) :
    exactCellBox m.val 15 p j = tabledCellBox m.val p j := by
  unfold exactCellBox tabledCellBox
  rw [exactTaylorMassBox_eq_tabled m p j hj]
  have he := (quadrature_node_checks m ⟨j,hj⟩).2
  unfold quadratureErrorComputation at he
  rw [he]

theorem exactFiniteModeBox_eq_tabled (m : Fin 3) (p : ℕ) :
    exactFiniteModeBox m.val 15 p = tabledFiniteModeBox m.val p := by
  unfold exactFiniteModeBox tabledFiniteModeBox
  exact Box.sum_congr _ _ _ (fun j hj => exactCellBox_eq_tabled m p j hj)

theorem exactFullModeBox_eq_tabled (m : Fin 3) (p : ℕ) :
    exactFullModeBox m.val 15 p = tabledFullModeBox m.val p := by
  unfold exactFullModeBox tabledFullModeBox
  rw [exactFiniteModeBox_eq_tabled m p]

theorem exactFullThetaMomentBox_eq_tabled (p : ℕ) :
    exactFullThetaMomentBox p = tabledFullThetaMomentBox p := by
  unfold exactFullThetaMomentBox tabledFullThetaMomentBox
  have h0 := exactFullModeBox_eq_tabled (0:Fin 3) p
  have h1 := exactFullModeBox_eq_tabled (1:Fin 3) p
  have h2 := exactFullModeBox_eq_tabled (2:Fin 3) p
  norm_num at h0 h1 h2
  rw [h0,h1,h2]

theorem mem_tabledFullThetaMomentBox (p : ℕ) (hp : p ≤ 18) :
    (tabledFullThetaMomentBox p).Mem
      (CarrySelfAdjointOperator.completedNativeThetaTailMoment p) := by
  have h := mem_exactFullThetaMomentBox p hp
  rw [exactFullThetaMomentBox_eq_tabled] at h
  exact h

end CarryIntegralCertificate
