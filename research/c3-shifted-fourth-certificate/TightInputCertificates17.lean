import TightInputTable17

namespace C3ShiftedFourth

open CarryC3Boxes CarryC3Tail

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 30000000
set_option maxRecDepth 30000

/-- Original-source amplitude boxes for the 265 M=80 sample addresses. The
first 205 use the exact low-address `expBox` cache; the last 60 reuse the
already checked M=80 source table. -/
def tightM80AmplitudeBox (n : Fin 265) : Box :=
  if h : n.val < 205 then
    tightLowSampleAmplitudeReference17 ⟨n.val, h⟩
  else
    tightHighSampleAmplitudeReference ⟨n.val-205, by omega⟩

/-- Original-source logarithm boxes for the same M=80 addresses. -/
def tightM80LogBox (n : Fin 265) : Box :=
  if h : n.val < 205 then
    tightLowSampleLogReference17 ⟨n.val, h⟩
  else
    tightHighSampleLogBox ⟨n.val-205, by omega⟩

/-- The generated low logarithm cache is checked against the exact rational
series evaluator used by the original source proof. -/
theorem tight_low_sample_log_evaluator_eq (n : Fin 205) :
    rationalLogBox (n.val+1) (Nat.log2 (n.val+1)+1) =
      tightLowSampleLogReference17 n := by
  fin_cases n <;> decide +kernel

/-- The generated low amplitude cache is checked against the exact original
64-term interval exponential evaluator. -/
theorem tight_low_sample_amplitude_evaluator_check (n : Fin 205) :
    (expBox (bmul (Box.point (-1/2)) (tightLowSampleLogReference17 n))).Subset
      (tightLowSampleAmplitudeReference17 n) := by
  fin_cases n <;> decide +kernel

theorem tight_m80_log_box_contains (n : Fin 265) :
    (tightM80LogBox n).Contains (Real.log (n.val+1:ℕ)) := by
  by_cases hn : n.val < 205
  · let k : Fin 205 := ⟨n.val, hn⟩
    have hsrc : (rationalLogBox (n.val+1) (Nat.log2 (n.val+1)+1)).Contains
        (Real.log (n.val+1:ℕ)) := by
      simpa [tightSampleLogBox, hn] using tight_sample_log_contains n
    rw [tight_low_sample_log_evaluator_eq k] at hsrc
    simpa [tightM80LogBox, hn, k] using hsrc
  · let k : Fin 60 := ⟨n.val-205, by omega⟩
    have hsrc := tight_sample_log_contains n
    have heq : tightSampleLogBox n = tightHighSampleLogBox k := by
      simp [tightSampleLogBox, hn, k]
    rw [heq] at hsrc
    simpa [tightM80LogBox, hn, k] using hsrc

theorem tight_m80_amplitude_box_contains (n : Fin 265) :
    (tightM80AmplitudeBox n).Contains
      (Real.exp (-Real.log (n.val+1:ℕ)/2)) := by
  by_cases hn : n.val < 205
  · let k : Fin 205 := ⟨n.val, hn⟩
    have hscaled := bmul_contains (Box.point_contains (-1/2))
      (tight_m80_log_box_contains n)
    have hscaled' : (bmul (Box.point (-1/2))
        (tightLowSampleLogReference17 k)).Contains
        (-Real.log (n.val+1:ℕ)/2) := by
      have he : ((-1/2:ℚ):ℝ)*Real.log (n.val+1:ℕ) =
          -Real.log (n.val+1:ℕ)/2 := by norm_num; ring
      have hscaled0 : (bmul (Box.point (-1/2))
          (tightLowSampleLogReference17 k)).Contains
          (((-1/2:ℚ):ℝ)*Real.log (n.val+1:ℕ)) := by
        simpa [tightM80LogBox, hn, k] using hscaled
      rw [he] at hscaled0
      exact hscaled0
    have hboxeq : bmul (Box.point (-1/2)) (tightLowSampleLogReference17 k) =
        tightSampleScaledLogBox n := by
      calc
        _ = bmul (Box.point (-1/2))
            (rationalLogBox (n.val+1) (Nat.log2 (n.val+1)+1)) := by
              rw [← tight_low_sample_log_evaluator_eq k]
        _ = tightSampleScaledLogBox n := by
              simp [tightSampleScaledLogBox, tightSampleLogBox, hn]
    have hrange := tight_sample_scaled_log_range n
    rw [← hboxeq] at hrange
    have he := exp_box hscaled' hrange.1 hrange.2
    have h := Box.subset_contains
      (tight_low_sample_amplitude_evaluator_check k) he
    simpa [tightM80AmplitudeBox, hn, k] using h
  · let k : Fin 60 := ⟨n.val-205, by omega⟩
    have hsrc := tight_high_sample_amplitude_contains k
    have haddr : k.val+206=n.val+1 := by dsimp [k]; omega
    rw [haddr] at hsrc
    simpa [tightM80AmplitudeBox, hn, k] using hsrc

#print axioms tight_low_sample_log_evaluator_eq
#print axioms tight_low_sample_amplitude_evaluator_check
#print axioms tight_m80_log_box_contains
#print axioms tight_m80_amplitude_box_contains

end
end C3ShiftedFourth
