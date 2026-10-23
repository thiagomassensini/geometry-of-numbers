import CarrySelfAdjointOperator.CompletedC3BracketTfvdGreenFactorization
import CarrySelfAdjointOperator.CompletedNativeRealWeylMoments

namespace CarrySourceBezout.NativeTrace
open CarrySelfAdjointOperator CPFormal.Analytic.Cp
open Filter Topology
open scoped BigOperators ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

/-- Existing trace projection, linear in the ordinary/log coordinates of the
retained enriched TFVD state. It is not a new source or a positive metric. -/
def tracePiece (z T L : ℂ) : ℂ × ℂ :=
  (nativeXiCompletionFactor z*(T/cpChartFactor 3 (operatorHeightParameter z)),
   nativeXiCompletionBoundaryCompanion z*(T/cpChartFactor 3 (operatorHeightParameter z))+
    nativeXiCompletionFactor z*Complex.I*
      ((L*cpChartFactor 3 (operatorHeightParameter z)+
        T*deriv (cpChartFactor 3) (operatorHeightParameter z))/
          cpChartFactor 3 (operatorHeightParameter z)^2))

def headTrace (M : ℕ) (z : ℂ) : ℂ × ℂ :=
  let state := canonicalC3BracketTfvdCompletionState M (operatorHeightParameter z)
  tracePiece z state.transport.valueReadout state.transport.logJetReadout

def tailTrace (M : ℕ) (z : ℂ) : ℂ × ℂ :=
  let state := canonicalC3BracketTfvdCompletionState M (operatorHeightParameter z)
  tracePiece z state.valueTail state.logJetTail

/-- Both traces are assembled before any jet/diagonal projection. No
nonvanishing assumption on a finite head is used. -/
theorem tracePiece_add (z T L U V : ℂ) :
    tracePiece z (T+U) (L+V) = tracePiece z T L + tracePiece z U V := by
  apply Prod.ext <;> simp only [tracePiece,Prod.fst_add,Prod.snd_add] <;> ring

theorem stateTrace_head_tail (M : ℕ) (z : ℂ) :
    canonicalC3BracketTfvdCompletedTracePair M z = headTrace M z+tailTrace M z := by
  unfold headTrace tailTrace
  rw [← tracePiece_add]
  apply Prod.ext
  · rfl
  · unfold tracePiece canonicalC3BracketTfvdCompletedTracePair
      canonicalC3BracketTfvdBoundaryCompanion canonicalC3BracketTfvdNormalizedLogJetReadout
      canonicalC3BracketTfvdNormalizedValueReadout
    dsimp [CanonicalC3BracketTfvdCompletionState.valueReadout,
      CanonicalC3BracketTfvdCompletionState.logJetReadout]
    ring

/-- This is the SAME `(F,-F')` projection from the canonical enriched state.
Its Green port and both tail fields have not been redefined or removed. -/
theorem completedTrace_head_tail (M : ℕ) (z : ℂ)
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip) :
    (completedNativeOperatorCharacteristic z,-deriv completedNativeOperatorCharacteristic z) =
      headTrace M z+tailTrace M z := by
  rw [← stateTrace_head_tail,
    canonicalC3BracketTfvdCompletedTracePair_eq_F_negFprime M hz]

/-- Native completion and native chart, kept at the original center. -/
def valueMultiplier (z : ℂ) : ℂ :=
  nativeXiCompletionFactor z/cpChartFactor 3 (operatorHeightParameter z)

/-- A whole original C3 center/two-leg cell, after the same fixed linear trace projection. -/
def completedCell (m : ℕ) (z : ℂ) : ℂ :=
  valueMultiplier z*realCpSaturatedBracket 3 m (operatorHeightParameter z)

theorem head_value_formula (M : ℕ) (z : ℂ) :
    (headTrace M z).1 = valueMultiplier z*finiteBracketedDirichletChart 3 M (operatorHeightParameter z) := by
  rw [headTrace,tracePiece]
  dsimp only
  rw [(canonicalC3BracketTfvdCompletionState_transport_components M (operatorHeightParameter z)).1]
  unfold valueMultiplier
  ring

/-- Literal cell prefix with the original unit seed, NOT a moment-generated state. -/
theorem head_value_seed_cells (M : ℕ) (z : ℂ) :
    (headTrace M z).1 = valueMultiplier z + ∑ m ∈ Finset.range M, completedCell m z := by
  rw [head_value_formula,finiteBracketedDirichletChart_three_eq_one_add_trace]
  simp only [finiteCanonicalBracketTrace,mul_add,mul_one,Finset.mul_sum,completedCell]

theorem head_value_succ (M : ℕ) (z : ℂ) :
    (headTrace (M+1) z).1 = (headTrace M z).1+completedCell M z := by
  rw [head_value_seed_cells,head_value_seed_cells,Finset.sum_range_succ]
  ring

theorem value_multiplier_analytic_at (w : ℂ) (hw : ‖w‖ < (1/2:ℝ)) :
    AnalyticAt ℂ valueMultiplier w := by
  have hd : DifferentiableOn ℂ valueMultiplier (Metric.ball 0 (1/2:ℝ)) := by
    intro v hv
    have hn : ‖v‖ < (1/2:ℝ) := by simpa using hv
    have hs : operatorHeightParameter v ∈ genuineCriticalStrip := by
      have hi := Complex.abs_im_le_norm v
      norm_num [genuineCriticalStrip,operatorHeightParameter,Complex.mul_re]
      constructor <;> linarith [le_abs_self v.im,neg_abs_le v.im]
    have hp : DifferentiableAt ℂ operatorHeightParameter v := by unfold operatorHeightParameter; fun_prop
    have hc : DifferentiableAt ℂ (fun w => cpChartFactor 3 (operatorHeightParameter w)) v := by
      unfold cpChartFactor
      fun_prop
    exact ((nativeXiCompletionFactor_differentiableAt hs).div hc
      (canonicalC3ChartFactorHeight_ne_zero hs)).differentiableWithinAt
  exact hd.analyticAt (Metric.isOpen_ball.mem_nhds (by simpa using hw))

theorem valueMultiplier_analytic : AnalyticAt ℂ valueMultiplier 0 :=
  value_multiplier_analytic_at 0 (by norm_num)

theorem head_value_analytic (M : ℕ) : AnalyticAt ℂ (fun z => (headTrace M z).1) 0 := by
  have hT : Differentiable ℂ (finiteBracketedDirichletChart 3 M) :=
    fun s => (hasDerivAt_finiteBracketedDirichletChart_three_eq_neg_logJet M s).differentiableAt
  have hp : AnalyticAt ℂ operatorHeightParameter 0 := by
    unfold operatorHeightParameter
    fun_prop
  exact (valueMultiplier_analytic.mul ((hT.analyticAt _).comp hp)).congr
    (Eventually.of_forall (fun z => (head_value_formula M z).symm))

theorem completedCell_analytic (m : ℕ) : AnalyticAt ℂ (completedCell m) 0 := by
  have he : completedCell m = fun z => (headTrace (m+1) z).1-(headTrace m z).1 := by
    funext z
    rw [head_value_succ]
    ring
  rw [he]
  exact (head_value_analytic (m+1)).sub (head_value_analytic m)

theorem full_value_eventually_head_tail (M : ℕ) :
    completedNativeOperatorCharacteristic =ᶠ[nhds (0:ℂ)]
      (fun z => (headTrace M z).1+(tailTrace M z).1) := by
  filter_upwards [isOpen_completedNativeHeightDomain.mem_nhds
    zero_mem_completedNativeHeightDomain] with z hz
  exact congrArg Prod.fst (completedTrace_head_tail M z hz)

theorem tail_value_analytic (M : ℕ) : AnalyticAt ℂ (fun z => (tailTrace M z).1) 0 := by
  have hF := completedNativeOperatorCharacteristic_analyticAt zero_mem_completedNativeHeightDomain
  apply (hF.sub (head_value_analytic M)).congr
  filter_upwards [full_value_eventually_head_tail M] with z hz
  simp only [Pi.sub_apply]
  rw [hz]
  ring

/-- Taylor coefficients after the complete trace projection; all factors retained. -/
def sourceJet (r : ℕ) (f : ℂ → ℂ) : ℂ := iteratedDeriv r f 0/(r.factorial:ℂ)

theorem sourceJet_add (r : ℕ) (f g : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    sourceJet r (fun z => f z+g z) = sourceJet r f+sourceJet r g := by
  unfold sourceJet
  change iteratedDeriv r (f+g) 0/(r.factorial:ℂ) = _
  rw [iteratedDeriv_add hf.contDiffAt hg.contDiffAt,add_div]


end
end CarrySourceBezout.NativeTrace
