import DampedCamera
import SchurLogic

/-! The residual is the SAME one from PR #41. Its monic algebraic construction
precedes the sign question. The inverse version needs IsUnit, never PosDef. -/
namespace CarryJetOverlap
open CarrySelfAdjointOperator CarryFiberTransport ChiralReturn CPFormal.Analytic.Cp
open NativeMomentOrthogonalization GeometryOfNumbers.Analysis
open scoped BigOperators InnerProductSpace ComplexConjugate Matrix
open Filter Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

private theorem budget_close_of_boundary_energy (N : ℕ) (x : Fin (2*N) → ℂ)
    (d : ℝ) (he : nativeSourceFiniteBoundaryEnergy (2*N) x=4*d)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ hs : strip k (2*N), |(jetBudget N k x x hs).re-d|<ε := by
  have hlimit := nativeSourceProjectiveBoundaryJetSynthesis_energy_tendsto N x
  rw [he] at hlimit
  have hnear := Metric.tendsto_nhds.mp hlimit (4*ε) (by positivity)
  filter_upwards [hnear,canonicalCompletedNativeRadialProjectiveChiral_eventually_regular (2*N)]
    with k hk hreg
  intro hs
  rw [Real.dist_eq,← jetBudget_energy N k x hs (fun i => (hreg i).2.2)] at hk
  have hf : 4*(jetBudget N k x x hs).re-4*d=4*((jetBudget N k x x hs).re-d) := by ring
  rw [hf,abs_mul] at hk
  rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)] at hk
  linarith

/-- No sign and no invertibility: substitute the canonical PR41 polynomial
residual into the complete native budget, without replacing either source. -/
theorem pr41_residual_exact_budget (s : Fin 2) (n k : ℕ)
    (hs : strip k (2*(n+1))) :
    jetBudget (n+1) k (nativeResidualBoundary s n) (nativeResidualBoundary s n) hs=
      dampedCameraBalance k
        (nativeSourceChiralJetInput (n+1) k (nativeResidualBoundary s n))
        (nativeSourceChiralJetInput (n+1) k (nativeResidualBoundary s n)) hs+
      variableDefect k
        (nativeSourceChiralJetInput (n+1) k (nativeResidualBoundary s n))
        (nativeSourceChiralJetInput (n+1) k (nativeResidualBoundary s n)) hs :=
  jetBudget_eq_damped_add_defect _ _ _ _ _

/-- The residual of algebraic orthogonalization, including zero and negative
pivots, is recovered by the combined source budget in BOTH sectors. -/
theorem pr41_residual_budget_eventually_close (s : Fin 2) (n : ℕ)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ hs : strip k (2*(n+1)),
      |(jetBudget (n+1) k (nativeResidualBoundary s n) (nativeResidualBoundary s n) hs).re-
        carryPairingPivot (hankelPairing
          (fun j => canonicalCompletedNativeLogDerivativeMoment (j+s.val))) n|<ε :=
  budget_close_of_boundary_energy (n+1) (nativeResidualBoundary s n) _
    (nativeResidualBoundary_energy s n) ε hε

/-- Exact inverse-Schur direction of PR41: invertibility suffices for this
limit identity. No positive prefix or positive new pivot is assumed. -/
theorem pr41_inverseSchur_budget_eventually_close (s : Fin 2) (n : ℕ)
    (hA : IsUnit (sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment s.val n))
    (ε : ℝ) (hε : 0 < ε) :
    let a : Fin (n+1) → ℝ := Fin.snoc
      (-((sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment s.val n)⁻¹ *ᵥ
        sourceMomentCoupling canonicalCompletedNativeLogDerivativeMoment s.val n)) 1
    let x := if s=0 then nativeSourceBoundaryFromParity (n+1) (fun i => (a i : ℂ)) 0
      else nativeSourceBoundaryFromParity (n+1) 0 (fun i => (a i : ℂ))
    ∀ᶠ k : ℕ in atTop, ∀ hs : strip k (2*(n+1)),
      |(jetBudget (n+1) k x x hs).re-
        sourceMomentSchur canonicalCompletedNativeLogDerivativeMoment s.val n|<ε := by
  dsimp only
  exact budget_close_of_boundary_energy (n+1) _ _
    (native_inverseSchur_boundary_energy s n hA) ε hε

end
end CarryJetOverlap
