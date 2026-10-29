import NegativeTransport
import CarrySelfAdjointOperator.NativePhysicalTfvdSecondPort

namespace CarryTfvdCritical
open CarrySelfAdjointOperator PhysicalSewing NativeLaguerre ChiralReturn
open scoped BigOperators Matrix ComplexConjugate InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- The unchanged finite Cauchy pairing has conjugate symmetry. -/
theorem cauchy_pairing_swap (N : ℕ) (v e : Fin N → ℂ) :
    matrixPairing (cauchyMatrix N) e v = conj (matrixPairing (cauchyMatrix N) v e) := by
  have hi := inner_conj_symm (𝕜 := ℂ) (radialIncidentSynthesis 0 N e) (radialIncidentSynthesis 0 N v)
  simpa only [incident_inner_eq_matrixPairing, Nat.cast_zero, zero_add, one_mul] using hi.symm

/-- Keep both independent inputs and the whole original pair before contraction. -/
theorem secondPort_pairing_change (N k : ℕ) (v s w t e f : Fin N → ℂ) :
    canonicalCompletedNativeProjectiveChiralForm
      (twoPortSynthesis N k v (s+e)) (twoPortSynthesis N k w (t+f)) -
    canonicalCompletedNativeProjectiveChiralForm
      (twoPortSynthesis N k v s) (twoPortSynthesis N k w t) =
    (Complex.I*((k : ℂ)+1)/2) *
      (matrixPairing (cauchyMatrix N) e w - matrixPairing (cauchyMatrix N) v f) := by
  rw [twoPort_signed_form, twoPort_signed_form]
  simp only [matrixPairing, star_add, Matrix.mulVec_add, add_dotProduct, dotProduct_add]
  ring

/-- A readout of the OLD signed form, not a new positive metric. -/
def portFlux (N k : ℕ) (v s : Fin N → ℂ) : ℝ :=
  ((k : ℝ)+1) * (matrixPairing (cauchyMatrix N) v s).im

theorem twoPort_real_self (N k : ℕ) (v s : Fin N → ℂ) :
    (canonicalCompletedNativeProjectiveChiralForm
      (twoPortSynthesis N k v s) (twoPortSynthesis N k v s)).re = portFlux N k v s := by
  rw [twoPort_signed_form, cauchy_pairing_swap]
  unfold portFlux
  norm_num [Complex.mul_re, Complex.mul_im, div_eq_mul_inv]
  ring

theorem portFlux_add (N k : ℕ) (v s e : Fin N → ℂ) :
    portFlux N k v (s+e) = portFlux N k v s + portFlux N k v e := by
  simp only [portFlux,matrixPairing,Matrix.mulVec_add,dotProduct_add,Complex.add_im]
  ring

theorem twoPort_real_change (N k : ℕ) (v s e : Fin N → ℂ) :
    (canonicalCompletedNativeProjectiveChiralForm
      (twoPortSynthesis N k v (s+e)) (twoPortSynthesis N k v (s+e))).re -
    (canonicalCompletedNativeProjectiveChiralForm
      (twoPortSynthesis N k v s) (twoPortSynthesis N k v s)).re = portFlux N k v e := by
  rw [twoPort_real_self,twoPort_real_self,portFlux_add]
  ring

/-- No division by the finite HEAD value: only full physical denominators are required. -/
theorem tfvd_head_cross_residual (M : ℕ) (z : ℂ)
    (state : CanonicalC3BracketTfvdCompletionState M)
    (hQ : CPFormal.Analytic.Cp.cpChartFactor 3 (operatorHeightParameter z) ≠ 0)
    (hXi : nativeXiCompletionFactor z ≠ 0) (hT : state.valueReadout ≠ 0) :
    state.valueReadout *
      (state.transport.valueReadout * (tfvdStateResponse z state -
        (nativeXiCompletionBoundaryCompanion z / nativeXiCompletionFactor z +
          Complex.I * deriv (CPFormal.Analytic.Cp.cpChartFactor 3) (operatorHeightParameter z) /
            CPFormal.Analytic.Cp.cpChartFactor 3 (operatorHeightParameter z))) -
        Complex.I * state.transport.logJetReadout) =
      Complex.I * (state.transport.valueReadout * state.logJetTail -
        state.transport.logJetReadout * state.valueTail) := by
  have hs : tfvdStateResponse z state -
        (nativeXiCompletionBoundaryCompanion z / nativeXiCompletionFactor z +
          Complex.I * deriv (CPFormal.Analytic.Cp.cpChartFactor 3) (operatorHeightParameter z) /
            CPFormal.Analytic.Cp.cpChartFactor 3 (operatorHeightParameter z)) =
      Complex.I * state.logJetReadout / state.valueReadout := by
    rw [tfvdStateResponse_threeChannels z state hQ hXi hT]
    ring
  rw [hs]
  have hc : state.valueReadout *
      (state.transport.valueReadout * (Complex.I * state.logJetReadout / state.valueReadout) -
        Complex.I * state.transport.logJetReadout) =
      state.transport.valueReadout * Complex.I * state.logJetReadout -
        state.valueReadout * Complex.I * state.transport.logJetReadout := by
    field_simp
  rw [hc]
  simp only [CanonicalC3BracketTfvdCompletionState.valueReadout,
    CanonicalC3BracketTfvdCompletionState.logJetReadout]
  ring

end
end CarryTfvdCritical
