import SourceBlocks
import SourceSchur
import LiteralBudgetLimit
import LiteralCompanion
import CompanionJets
import Repartition
import NativeRepartition64

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

#check native_regrouped64_interval_margin
#check native_regrouped64_total_lower
#check native_second_even_balance_lower_from_original_split
#check native_second_even_remainder_pos_from_original_split
#check native_second_even_pivot_pos_from_original_split
