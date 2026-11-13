import GridJetTable17
import GridHeadEvaluation17

namespace C3ShiftedFourth

open CarryC3Boxes CarryC3Tail

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 30000000
set_option maxRecDepth 30000

def gridM80SampleJetReference17 (r : Fin 17) : Fin 265 → GridBox :=
  match r.val with
  | 0 => gridM80SampleJet0Reference17
  | 1 => gridM80SampleJet1Reference17
  | 2 => gridM80SampleJet2Reference17
  | 3 => gridM80SampleJet3Reference17
  | 4 => gridM80SampleJet4Reference17
  | 5 => gridM80SampleJet5Reference17
  | 6 => gridM80SampleJet6Reference17
  | 7 => gridM80SampleJet7Reference17
  | 8 => gridM80SampleJet8Reference17
  | 9 => gridM80SampleJet9Reference17
  | 10 => gridM80SampleJet10Reference17
  | 11 => gridM80SampleJet11Reference17
  | 12 => gridM80SampleJet12Reference17
  | 13 => gridM80SampleJet13Reference17
  | 14 => gridM80SampleJet14Reference17
  | 15 => gridM80SampleJet15Reference17
  | 16 => gridM80SampleJet16Reference17
  | _ => fun _ => GridBox.ofBox (Box.point 0)

def gridM80HeadReference17 (r : Fin 17) : GridBox :=
  match r.val with
  | 0 => gridM80Head0Reference17
  | 1 => gridM80Head1Reference17
  | 2 => gridM80Head2Reference17
  | 3 => gridM80Head3Reference17
  | 4 => gridM80Head4Reference17
  | 5 => gridM80Head5Reference17
  | 6 => gridM80Head6Reference17
  | 7 => gridM80Head7Reference17
  | 8 => gridM80Head8Reference17
  | 9 => gridM80Head9Reference17
  | 10 => gridM80Head10Reference17
  | 11 => gridM80Head11Reference17
  | 12 => gridM80Head12Reference17
  | 13 => gridM80Head13Reference17
  | 14 => gridM80Head14Reference17
  | 15 => gridM80Head15Reference17
  | 16 => gridM80Head16Reference17
  | _ => GridBox.ofBox (Box.point 0)

private theorem grid_sample_jet_table_bound (r : Fin 17) (n : Fin 265) :
    (gridM80SampleJetBox n r.val).toBox.Subset
      (gridM80SampleJetReference17 r n).toBox := by
  fin_cases r <;> fin_cases n <;> decide +kernel

theorem grid_sample_jet_reference17_contains (r : Fin 17) (n : Fin 265) :
    (gridM80SampleJetReference17 r n).toBox.Contains
      (sampleRealJet (n.val+1) r.val) := by
  exact Box.subset_contains (grid_sample_jet_table_bound r n)
    (grid_m80_sample_jet_box n r.val)

def gridM80HeadBox17 (r : Fin 17) : GridBox :=
  gridHead80JetBoxFrom (gridM80SampleJetReference17 r) r.val

theorem grid_m80_head_box17_contains (r : Fin 17) :
    (gridM80HeadBox17 r).toBox.Contains (head80RealJet r.val) := by
  exact grid_head80_jet_box_from (gridM80SampleJetReference17 r) r.val
    (grid_sample_jet_reference17_contains r)

theorem grid_m80_head_box17_eq_reference (r : Fin 17) :
    gridM80HeadBox17 r = gridM80HeadReference17 r := by
  fin_cases r <;> decide +kernel

def certifiedHead80JetBox17 (n : ℕ) : Box :=
  if hn : n < 17 then (gridM80HeadReference17 ⟨n, hn⟩).toBox else Box.point 0

theorem certified_head80_jet_box17_contains (n : ℕ) (hn : n < 17) :
    (certifiedHead80JetBox17 n).Contains (head80RealJet n) := by
  simp [certifiedHead80JetBox17, hn]
  rw [← grid_m80_head_box17_eq_reference ⟨n, hn⟩]
  exact grid_m80_head_box17_contains ⟨n, hn⟩

theorem tight_head80_jet14_box17 :
    (certifiedHead80JetBox17 14).Contains (head80RealJet 14) :=
  certified_head80_jet_box17_contains 14 (by omega)

theorem tight_head80_jet16_box17 :
    (certifiedHead80JetBox17 16).Contains (head80RealJet 16) :=
  certified_head80_jet_box17_contains 16 (by omega)

#print axioms grid_sample_jet_reference17_contains
#print axioms grid_m80_head_box17_contains
#print axioms certified_head80_jet_box17_contains
#print axioms tight_head80_jet14_box17
#print axioms tight_head80_jet16_box17

end
end C3ShiftedFourth
