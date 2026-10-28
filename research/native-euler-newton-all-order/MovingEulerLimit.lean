import NativeEulerTransport

namespace CarryEulerNewtonAll
open CarrySelfAdjointOperator CarryNativeBinomial CarrySelfAdjointOperator.ChiralReturn
open Filter Topology
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem euler_newton_continuous (N : ℕ) :
    Continuous (fun p : ℝ × (Fin N → ℂ) => eulerNewton N p.1 p.2) := by
  apply continuous_pi
  intro m
  unfold eulerNewton
  simp only [Matrix.mulVec, dotProduct, eulerNewtonMatrix]
  fun_prop

/-- Moving Euler vectors are transported in the finite vector space BEFORE
any energy readout. This does not assert convergence of physical states. -/
theorem euler_newton_path_tendsto (N : ℕ) (v : ℕ → Fin N → ℂ) (w : Fin N → ℂ)
    (hv : Tendsto v atTop (nhds w)) :
    Tendsto (fun k => eulerNewton N (radialFourSourceStep k) (v k)) atTop
      (nhds (fun m : Fin N => (Real.sqrt 2:ℂ)*nativeSourceJetOrderPhase m*Complex.I^(m:ℕ)*w m)) := by
  have ht := (euler_newton_continuous N).continuousAt.tendsto.comp
    (radialFourSourceStep_tendsto_zero.prodMk_nhds hv)
  simpa only [Function.comp_def, euler_newton_at_zero] using ht

/-- A moving ORIGINAL source with convergent Euler chart has the prescribed
Newton-coordinate limit; no moments or positivity define those vectors. -/
theorem source_newton_path_tendsto (n : ℕ) (x : ℕ → ℕ →₀ ℂ) (w : Fin (2*n) → ℂ)
    (hv : Tendsto (fun k => physicalEulerChart n k (x k)) atTop (nhds w)) :
    Tendsto (fun k => newtonCoordinates n k (fun r : Fin (2*n) => x k r)) atTop
      (nhds (fun m : Fin (2*n) => (Real.sqrt 2:ℂ)*nativeSourceJetOrderPhase m*Complex.I^(m:ℕ)*w m)) := by
  have ht := euler_newton_path_tendsto (2*n) (fun k => physicalEulerChart n k (x k)) w hv
  have he : (fun k => eulerNewton (2*n) (radialFourSourceStep k) (physicalEulerChart n k (x k)))
      =ᶠ[atTop] (fun k => newtonCoordinates n k (fun r : Fin (2*n) => x k r)) := by
    filter_upwards [source_euler_newton_eventually_all_order n] with k hk
    exact hk (x k)
  exact ht.congr' he

/-- The coefficient norm in the existing native error estimate is controlled
along these moving source paths. The physical Cauchy norm is not replaced. -/
theorem source_newton_path_eventually_bounded (n : ℕ) (x : ℕ → ℕ →₀ ℂ)
    (w : Fin (2*n) → ℂ)
    (hv : Tendsto (fun k => physicalEulerChart n k (x k)) atTop (nhds w)) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ k : ℕ in atTop,
      ‖newtonCoordinates n k (fun r : Fin (2*n) => x k r)‖≤C := by
  let y : Fin (2*n) → ℂ := fun m =>
    (Real.sqrt 2:ℂ)*nativeSourceJetOrderPhase m*Complex.I^(m:ℕ)*w m
  have ht : Tendsto (fun k => newtonCoordinates n k (fun r : Fin (2*n) => x k r))
      atTop (nhds y) := source_newton_path_tendsto n x w hv
  refine ⟨‖y‖+1, by positivity, ?_⟩
  filter_upwards [(Metric.tendsto_nhds.1 ht) 1 (by norm_num)] with k hk
  have hb : ‖newtonCoordinates n k (fun r : Fin (2*n) => x k r)-y‖<1 := by
    simpa only [dist_eq_norm] using hk
  have htri := norm_add_le
    (newtonCoordinates n k (fun r : Fin (2*n) => x k r)-y) y
  simp only [sub_add_cancel] at htri
  linarith

end
end CarryEulerNewtonAll
