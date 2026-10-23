import FourJetWitness

open CarryTwoEvenJets
open CarrySelfAdjointOperator
noncomputable section

-- AUXILIARY algebraic control: a pure-tail quartic can vanish while its
-- mixed contribution is nonzero. It is not a new physical source.
example : quartic (fun j : Fin 4 => if j.val=3 then 1 else 0) = 0 := by
  norm_num [quartic,polarizedQuartic]

example : quarticFlux (fun _ : Fin 4 => 1) (fun j => if j.val=3 then 1 else 0) = 3 := by
  norm_num [quarticFlux,polarizedQuartic]

#check native_real_tfvd_ledger
#check canonical_two_even_det_pos_of_four_jet_boxes
#check native_two_even_critical_residual
