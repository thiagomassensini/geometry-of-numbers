import UniformMovingError

namespace CarryMovingEulerBalance
open CarrySelfAdjointOperator CarryNativeBinomial CarryEulerNewtonAll CarryTailReturn
open CarrySelfAdjointOperator.ChiralReturn CarrySelfAdjointOperator.PhysicalSewing
open CarrySelfAdjointOperator.NativeLaguerre
open Filter Topology
open scoped InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- Same complete source, same original boundary energy, every finite order.
Convergence and eventual support are explicit; no sign premise is added. -/
theorem physical_balance_tendsto (n : ℕ) (x : ℕ → ℕ →₀ ℂ)
    (w : Fin (2*n) → ℂ)
    (hx : ∀ᶠ k : ℕ in atTop, (x k).support ⊆ Finset.range (2*n))
    (hv : Tendsto (fun k => physicalEulerChart n k (x k)) atTop (nhds w)) :
    Tendsto (fun k => 4*(canonicalCompletedNativeProjectiveChiralForm
      (physicalCompletedFiniteSource k (x k)) (physicalCompletedFiniteSource k (x k))).re)
      atTop (nhds (nativeSourceFiniteBoundaryEnergy (2*n) (eulerNewton (2*n) 0 w))) := by
  have hy := source_newton_path_tendsto n x w hv
  rw [← euler_newton_at_zero] at hy
  have he := (nativeSourceFiniteBoundaryEnergy_continuous (2*n)).continuousAt.tendsto.comp hy
  have hz := physical_balance_error_tendsto_zero n x w hx hv
  simpa only [Function.comp_def, sub_add_cancel, zero_add] using hz.add he

/-- Literal difference of the two physical channel energies. This fixes the
normalization: the difference tends to one HALF of the native boundary energy. -/
theorem physical_channel_balance_tendsto (n : ℕ) (x : ℕ → ℕ →₀ ℂ)
    (w : Fin (2*n) → ℂ)
    (hx : ∀ᶠ k : ℕ in atTop, (x k).support ⊆ Finset.range (2*n))
    (hv : Tendsto (fun k => physicalEulerChart n k (x k)) atTop (nhds w)) :
    Tendsto (fun k => ‖(physicalCompletedFiniteSource k (x k)).1‖^2-
      ‖(physicalCompletedFiniteSource k (x k)).2‖^2) atTop
      (nhds (nativeSourceFiniteBoundaryEnergy (2*n) (eulerNewton (2*n) 0 w)/2)) := by
  have ht := (physical_balance_tendsto n x w hx hv).div_const (2:ℝ)
  convert ht using 1
  funext k
  rw [← signed_diagonal_norm]
  ring

end
end CarryMovingEulerBalance
