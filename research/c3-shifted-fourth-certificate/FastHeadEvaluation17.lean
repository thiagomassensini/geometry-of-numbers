import HighSampleAmplitude17

namespace C3ShiftedFourth

open CarryC3Boxes CarryC3Tail
open scoped BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 30000000
set_option maxRecDepth 30000

def tightHighSampleJetBox (n : Fin 60) (r : ℕ) : Box :=
  bmul (tightHighSampleAmplitudeReference n)
    (bmul (bpow (bneg (tightHighSampleLogBox n)) r)
      (Box.point ((r.factorial:ℚ)⁻¹)))

theorem tight_high_sample_jet_box (n : Fin 60) (r : ℕ) :
    (tightHighSampleJetBox n r).Contains (sampleRealJet (n.val+206) r) := by
  let j : Fin 265 := ⟨n.val+205, by omega⟩
  have ha := tight_high_sample_amplitude_contains n
  have hlogEq : tightSampleLogBox j = tightHighSampleLogBox n := by
    simp [tightSampleLogBox, j]
  have hl := tight_sample_log_contains j
  rw [hlogEq] at hl
  have haddr : j.val+1 = n.val+206 := by simp [j]
  rw [haddr] at hl
  have h := bmul_contains ha
    (bmul_contains
      (bpow_contains (Box.neg_contains hl) r)
      (Box.point_contains ((r.factorial:ℚ)⁻¹)))
  simpa [tightHighSampleJetBox, sampleRealJet, div_eq_mul_inv,
    Rat.cast_inv, Rat.cast_natCast, bneg, mul_assoc] using h

def cachedM80SampleJetBox (n : Fin 265) (r : ℕ) : Box :=
  if hn : n.val < 205 then
    sampleJetBox ⟨n.val, hn⟩ r
  else
    tightHighSampleJetBox ⟨n.val-205, by omega⟩ r

theorem cached_m80_sample_jet_box (n : Fin 265) (r : ℕ) :
    (cachedM80SampleJetBox n r).Contains (sampleRealJet (n.val+1) r) := by
  by_cases hn : n.val < 205
  · simp [cachedM80SampleJetBox, hn]
    exact sample_jet_box ⟨n.val, hn⟩ r
  · simp only [cachedM80SampleJetBox, hn]
    let k : Fin 60 := ⟨n.val-205, by omega⟩
    have hk := tight_high_sample_jet_box k r
    have haddr : k.val+206=n.val+1 := by dsimp [k]; omega
    rw [haddr] at hk
    simpa [k] using hk

def tightHead80JetBoxCached (r : ℕ) : Box :=
  badd (badd (Box.point (if r=0 then 1 else 0))
    (bsumFin (fun m : Fin 80 =>
      badd (bsub (cachedM80SampleJetBox ⟨3*m.val+1, by omega⟩ r)
        (bmul (Box.point 2) (cachedM80SampleJetBox ⟨3*m.val+2, by omega⟩ r)))
        (cachedM80SampleJetBox ⟨3*m.val+3, by omega⟩ r))))
    (bsumFin (fun k : Fin 24 =>
      bmul (Box.point (boundary48Weight k))
        (cachedM80SampleJetBox ⟨241+k.val, by omega⟩ r)))

theorem tight_head80_jet_box_cached (r : ℕ) :
    (tightHead80JetBoxCached r).Contains (head80RealJet r) := by
  have hcell (m : Fin 80) :
      (badd (bsub (cachedM80SampleJetBox ⟨3*m.val+1, by omega⟩ r)
        (bmul (Box.point 2) (cachedM80SampleJetBox ⟨3*m.val+2, by omega⟩ r)))
        (cachedM80SampleJetBox ⟨3*m.val+3, by omega⟩ r)).Contains
        (sampleRealJet (3*m.val+2) r - 2*sampleRealJet (3*m.val+3) r +
          sampleRealJet (3*m.val+4) r) := by
    have h1 : 3*m.val+1+1=3*m.val+2 := by omega
    have h2 : 3*m.val+2+1=3*m.val+3 := by omega
    have h3 : 3*m.val+3+1=3*m.val+4 := by omega
    simpa only [Fin.val_mk, h1, h2, h3, Rat.cast_ofNat] using badd_contains
      (bsub_contains (cached_m80_sample_jet_box ⟨3*m.val+1, by omega⟩ r)
        (bmul_contains (Box.point_contains 2)
          (cached_m80_sample_jet_box ⟨3*m.val+2, by omega⟩ r)))
      (cached_m80_sample_jet_box ⟨3*m.val+3, by omega⟩ r)
  have hb (k : Fin 24) :
      (bmul (Box.point (boundary48Weight k))
        (cachedM80SampleJetBox ⟨241+k.val, by omega⟩ r)).Contains
        ((boundary48Weight k:ℝ)*sampleRealJet (242+k.val) r) := by
    have h : 241+k.val+1=242+k.val := by omega
    simpa only [Fin.val_mk, h] using
      bmul_contains (Box.point_contains (boundary48Weight k))
        (cached_m80_sample_jet_box ⟨241+k.val, by omega⟩ r)
  have hh := badd_contains
    (badd_contains (Box.point_contains (if r=0 then 1 else 0))
      (bsumFin_contains _ _ hcell))
    (bsumFin_contains _ _ hb)
  have he : (∑ m : Fin 80,
      (sampleRealJet (3*m.val+2) r-(2:ℝ)*sampleRealJet (3*m.val+3) r+
        sampleRealJet (3*m.val+4) r)) =
      ∑ m ∈ Finset.range 80,
        (sampleRealJet (3*m+2) r-2*sampleRealJet (3*m+3) r+
          sampleRealJet (3*m+4) r) := by
    exact Fin.sum_univ_eq_sum_range
      (fun m : ℕ => sampleRealJet (3*m+2) r-2*sampleRealJet (3*m+3) r+
        sampleRealJet (3*m+4) r) 80
  rw [he] at hh
  simpa only [tightHead80JetBoxCached, head80RealJet, Rat.cast_ofNat,
    apply_ite, Rat.cast_one, Rat.cast_zero] using hh

#print axioms tight_high_sample_amplitude_evaluator_check
#print axioms tight_high_sample_jet_box
#print axioms tight_head80_jet_box_cached


#print axioms tight_high_sample_jet_box
#print axioms tight_head80_jet_box_cached

end
end C3ShiftedFourth
