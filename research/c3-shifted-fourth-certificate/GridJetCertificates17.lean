import GridJetTable17
import GridHeadEvaluation17

namespace C3ShiftedFourth

open CarryC3Boxes CarryC3Tail

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 30000000
set_option maxRecDepth 30000

/-- The generated jet cache is checked entry-by-entry against the certified
source amplitude/log boxes and the integer-grid evaluator. -/
private theorem grid_sample_jet14_table_bound (n : Fin 265) :
    (gridM80SampleJetBox n 14).toBox.Subset
      (gridM80SampleJet14Reference17 n).toBox := by
  fin_cases n <;> decide +kernel

private theorem grid_sample_jet16_table_bound (n : Fin 265) :
    (gridM80SampleJetBox n 16).toBox.Subset
      (gridM80SampleJet16Reference17 n).toBox := by
  fin_cases n <;> decide +kernel

theorem grid_sample_jet14_reference_contains (n : Fin 265) :
    (gridM80SampleJet14Reference17 n).toBox.Contains (sampleRealJet (n.val+1) 14) := by
  exact Box.subset_contains (grid_sample_jet14_table_bound n)
    (grid_m80_sample_jet_box n 14)

theorem grid_sample_jet16_reference_contains (n : Fin 265) :
    (gridM80SampleJet16Reference17 n).toBox.Contains (sampleRealJet (n.val+1) 16) := by
  exact Box.subset_contains (grid_sample_jet16_table_bound n)
    (grid_m80_sample_jet_box n 16)

def gridM80Head14Box17 : GridBox :=
  gridHead80JetBoxFrom gridM80SampleJet14Reference17 14

def gridM80Head16Box17 : GridBox :=
  gridHead80JetBoxFrom gridM80SampleJet16Reference17 16

theorem grid_m80_head14_box17_contains :
    gridM80Head14Box17.toBox.Contains (head80RealJet 14) := by
  exact grid_head80_jet_box_from gridM80SampleJet14Reference17 14
    grid_sample_jet14_reference_contains

theorem grid_m80_head16_box17_contains :
    gridM80Head16Box17.toBox.Contains (head80RealJet 16) := by
  exact grid_head80_jet_box_from gridM80SampleJet16Reference17 16
    grid_sample_jet16_reference_contains

theorem grid_m80_head14_reference17_eq :
    gridM80Head14Box17 = gridM80Head14Reference17 := by
  decide +kernel

theorem grid_m80_head16_reference17_eq :
    gridM80Head16Box17 = gridM80Head16Reference17 := by
  decide +kernel

theorem tight_head80_jet14_box17 :
    (gridM80Head14Reference17.toBox).Contains (head80RealJet 14) := by
  rw [← grid_m80_head14_reference17_eq]
  exact grid_m80_head14_box17_contains

theorem tight_head80_jet16_box17 :
    (gridM80Head16Reference17.toBox).Contains (head80RealJet 16) := by
  rw [← grid_m80_head16_reference17_eq]
  exact grid_m80_head16_box17_contains

#print axioms grid_sample_jet14_reference_contains
#print axioms grid_sample_jet16_reference_contains
#print axioms tight_head80_jet14_box17
#print axioms tight_head80_jet16_box17

end
end C3ShiftedFourth
