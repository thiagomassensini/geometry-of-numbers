import LiteralTailBounds

namespace CarrySourceBezout
open CarrySelfAdjointOperator NativeTrace CPFormal.Analytic.Cp
noncomputable section
set_option maxHeartbeats 1800000

/-- The original completed companion is exactly negative differentiation of
the same trace value, before any coefficient/parity projection. -/
theorem tracePiece_companion (T L : ℂ → ℂ) (w : ℂ)
    (hs : operatorHeightParameter w ∈ genuineCriticalStrip)
    (hT : HasDerivAt T (-L (operatorHeightParameter w)) (operatorHeightParameter w)) :
    (tracePiece w (T (operatorHeightParameter w)) (L (operatorHeightParameter w))).2 =
      -deriv (fun z => nativeXiCompletionFactor z *
        (T (operatorHeightParameter z)/cpChartFactor 3 (operatorHeightParameter z))) w := by
  have hc := (differentiable_cpChartFactor 3 (by norm_num)).differentiableAt.hasDerivAt
    (x := operatorHeightParameter w)
  have hq := (hT.div hc (canonicalC3ChartFactorHeight_ne_zero hs)).comp w
    (hasDerivAt_operatorHeightParameter w)
  have hp := (nativeXiCompletionFactor_differentiableAt hs).hasDerivAt.mul hq
  change HasDerivAt (fun z => nativeXiCompletionFactor z *
    (T (operatorHeightParameter z)/cpChartFactor 3 (operatorHeightParameter z))) _ w at hp
  rw [hp.deriv]
  unfold tracePiece nativeXiCompletionBoundaryCompanion
  dsimp only [Function.comp_apply, Pi.div_apply]
  ring

theorem literal_head_companion (M : ℕ) (w : ℂ)
    (hs : operatorHeightParameter w ∈ genuineCriticalStrip) :
    (headTrace M w).2 = -deriv (fun z => (headTrace M z).1) w := by
  have he : (fun z => (headTrace M z).1) = fun z => nativeXiCompletionFactor z *
      (finiteBracketedDirichletChart 3 M (operatorHeightParameter z) /
        cpChartFactor 3 (operatorHeightParameter z)) := by
    funext z
    rw [head_value_formula]
    unfold valueMultiplier
    ring
  rw [he]
  have hc := tracePiece_companion (finiteBracketedDirichletChart 3 M)
    (finiteCanonicalLogBracketChart M) w hs
    (hasDerivAt_finiteBracketedDirichletChart_three_eq_neg_logJet M (operatorHeightParameter w))
  rw [headTrace]
  rw [(canonicalC3BracketTfvdCompletionState_transport_components M (operatorHeightParameter w)).1,
    (canonicalC3BracketTfvdCompletionState_transport_components M (operatorHeightParameter w)).2.1]
  exact hc

theorem literal_tail_companion (M : ℕ) (w : ℂ)
    (hs : operatorHeightParameter w ∈ genuineCriticalStrip) :
    (tailTrace M w).2 = -deriv (fun z => (tailTrace M z).1) w := by
  have he : (fun z => (tailTrace M z).1) = fun z => nativeXiCompletionFactor z *
      (realCpBracketCutoffTail 3 M (operatorHeightParameter z) /
        cpChartFactor 3 (operatorHeightParameter z)) := by
    funext z
    rw [literal_tail_value_formula]
    unfold valueMultiplier
    ring
  rw [he]
  have hhalf : operatorHeightParameter w ∈ bracketHalfPlane := by
    change -1 < (operatorHeightParameter w).re
    linarith [hs.1]
  exact tracePiece_companion (realCpBracketCutoffTail 3 M) (canonicalC3LogJetCutoffTail M) w hs
    (hasDerivAt_realCpBracketCutoffTail_eq_neg_logJetTail M hhalf)

end
end CarrySourceBezout
