import SourceBlocks
import SourceSchur
import LiteralBudgetLimit
import LiteralCompanion
import CompanionJets
import Repartition

open CarrySourceBezout CarrySelfAdjointOperator

-- The source-only and moment residuals are different, with this exact factor.
example (b : Bool) (n : ℕ)
    (hA : IsUnit (sourceMomentMatrix nativeH (if b then 1 else 0) n)) :
    sourceSchur nativeC b n =
      nativeC 0 * nativeSourceSchurRemainder (if b then 1 else 0) n :=
  native_sourceSchur_remainder b n hA

#check sourceDirection_transport
#check monicSourceDirection_eq_sourceCritical
#check sourceDirection_energy
#check monicSourceDirection_energy
#check native_residual_literal_four_terms
#check NativeTrace.stateTrace_head_tail
#check literal_head_companion
#check literal_tail_companion
#check literal_tail_jet_envelope
#check literal_error_budget_tendsto_zero
#check native_residual_repartition
#check negative_control_not_posSemidef

#check literal_head_response_odd
#check literal_tail_response_even_succ
