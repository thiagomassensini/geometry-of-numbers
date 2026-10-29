import MovingEulerLimit
import AllOrderEnergyControl
import CarrySelfAdjointOperator.CompletedNativeChiralReturnArbitraryOrder

namespace CarryMovingEulerBalance
open CarrySelfAdjointOperator CarryNativeBinomial CarryEulerNewtonAll
open CarrySelfAdjointOperator.ChiralReturn CarrySelfAdjointOperator.PhysicalSewing
open CarrySelfAdjointOperator.NativeLaguerre
open Filter Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- A uniform quadratic error becomes small along bounded coefficient paths.
The norm is supplied by the EXISTING coefficient space, not a new metric. -/
theorem uniform_quadratic_error_tendsto_zero {E : Type*} [SeminormedAddCommGroup E]
    (f g : ℕ → ℝ) (y : ℕ → E) (C : ℝ)
    (hb : ∀ᶠ k : ℕ in atTop, ‖y k‖≤C)
    (he : ∀ η : ℝ, 0<η → ∀ᶠ k : ℕ in atTop, |f k-g k|≤η*‖y k‖^2) :
    Tendsto (fun k => f k-g k) atTop (nhds 0) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  let η : ℝ := ε/(C^2+1)
  have hd : 0<C^2+1 := by positivity
  have hη : 0<η := div_pos hε hd
  have hηeq : η*(C^2+1)=ε := by dsimp [η]; field_simp
  have hsmall : η*C^2<ε := by nlinarith
  filter_upwards [hb, he η hη] with k hk herror
  have hs : ‖y k‖^2≤C^2 := pow_le_pow_left₀ (norm_nonneg _) hk 2
  have ht := herror.trans (mul_le_mul_of_nonneg_left hs hη.le)
  have hlt := lt_of_le_of_lt ht hsmall
  simpa only [Real.dist_eq, sub_zero] using hlt

/-- The complete physical balance and its ORIGINAL boundary readout differ
by an error tending to zero along convergent moving Euler charts. -/
theorem physical_balance_error_tendsto_zero (n : ℕ) (x : ℕ → ℕ →₀ ℂ)
    (w : Fin (2*n) → ℂ)
    (hx : ∀ᶠ k : ℕ in atTop, (x k).support ⊆ Finset.range (2*n))
    (hv : Tendsto (fun k => physicalEulerChart n k (x k)) atTop (nhds w)) :
    Tendsto (fun k =>
      4*(canonicalCompletedNativeProjectiveChiralForm
        (physicalCompletedFiniteSource k (x k)) (physicalCompletedFiniteSource k (x k))).re-
      nativeSourceFiniteBoundaryEnergy (2*n)
        (newtonCoordinates n k (fun r : Fin (2*n) => x k r))) atTop (nhds 0) := by
  obtain ⟨C,_hC,hb⟩ := source_newton_path_eventually_bounded n x w hv
  apply uniform_quadratic_error_tendsto_zero
    (y:=fun k => newtonCoordinates n k (fun r : Fin (2*n) => x k r))
    (C:=C) (hb:=hb)
  intro η hη
  filter_upwards [source_explicit_energy_control_all_order n η hη, hx] with k hk hs
  exact hk (x k) hs

end
end CarryMovingEulerBalance
