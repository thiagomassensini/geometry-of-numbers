import C3Head48Boxes
import ElementaryBoxes
import HighLogTable

namespace C3ShiftedFourth

open CarryC3Boxes CarryC3Tail
open scoped BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 20000000
set_option maxRecDepth 30000

/-- The existing 128-term rational logarithm evaluator, used directly instead
of the wider decimal target table for the C3/48 fourth-order calculation. -/
def tightSampleLogBox (n : Fin 265) : Box :=
  if h : n.val < 205 then
    rationalLogBox (n.val+1) (Nat.log2 (n.val+1)+1)
  else tightHighSampleLogBox ⟨n.val-205, by omega⟩

private theorem tight_sample_log_normalization (n : Fin 265) :
    (1/2:ℚ) ≤ (n.val+1:ℚ)/2^(Nat.log2 (n.val+1)+1) ∧
      (n.val+1:ℚ)/2^(Nat.log2 (n.val+1)+1) ≤ 1 := by
  let x := n.val+1
  have hx : x ≠ 0 := by simp [x]
  have hlog : Nat.log2 x = Nat.log 2 x := Nat.log2_eq_log_two
  have hpowl : 2^Nat.log2 x ≤ x := by
    rw [hlog]
    exact Nat.pow_log_le_self 2 hx
  have hpowu : x < 2^(Nat.log2 x+1) := by
    rw [hlog]
    exact Nat.lt_pow_succ_log_self Nat.one_lt_two x
  have hpowl' : (2:ℚ)^Nat.log2 x ≤ (x:ℚ) := by exact_mod_cast hpowl
  have hpowu' : (x:ℚ) ≤ (2:ℚ)^(Nat.log2 x+1) := by exact_mod_cast hpowu.le
  have hp : (2:ℚ)^(Nat.log2 x+1) = 2*(2:ℚ)^Nat.log2 x := by
    rw [pow_succ]
    ring
  have hp0 : (0:ℚ) < (2:ℚ)^(Nat.log2 x+1) := by positivity
  constructor
  · have hl : (1/2:ℚ) ≤ (x:ℚ)/(2:ℚ)^(Nat.log2 x+1) := by
      rw [le_div_iff₀ hp0, hp]
      norm_num
      nlinarith
    simpa [x] using hl
  · have hu : (x:ℚ)/(2:ℚ)^(Nat.log2 x+1) ≤ 1 := by
      rw [div_le_iff₀ hp0]
      simpa only [one_mul] using hpowu'
    simpa [x] using hu

theorem tight_sample_log_evaluator_check (n : Fin 265) :
    (rationalLogBox (n.val+1) (Nat.log2 (n.val+1)+1)).Subset
      (tightSampleLogBox n) := by
  by_cases hn : n.val < 205
  · simp only [tightSampleLogBox, dif_pos hn]
    exact ⟨le_rfl, le_rfl⟩
  · let k : Fin 60 := ⟨n.val-205, by omega⟩
    have hk := tight_high_sample_log_evaluator_check k
    have hval : k.val+206 = n.val+1 := by simp [k]; omega
    have hlog : Nat.log2 (n.val+1) = Nat.log2 (k.val+206) :=
      congrArg Nat.log2 hval.symm
    have harg : (n.val:ℚ)+1 = (k.val:ℚ)+206 := by
      exact_mod_cast hval.symm
    simp only [tightSampleLogBox, dif_neg hn]
    rw [harg, hlog]
    change (rationalLogBox (k.val+206) (Nat.log2 (k.val+206)+1)).Subset
      (tightHighSampleLogBox k)
    exact hk

theorem tight_sample_log_contains (n : Fin 265) :
    (tightSampleLogBox n).Contains (Real.log (n.val+1:ℕ)) := by
  apply Box.subset_contains (tight_sample_log_evaluator_check n)
  simpa only [Rat.cast_natCast, Rat.cast_add, Rat.cast_one,
    Nat.cast_add, Nat.cast_one] using
    rational_log_box (n.val+1) (Nat.log2 (n.val+1)+1)
      (tight_sample_log_normalization n)

def tightSampleScaledLogBox (n : Fin 265) : Box :=
  bmul (Box.point (-1/2)) (tightSampleLogBox n)

private theorem roundLower_mono {x y : ℚ} (h : x ≤ y) :
    roundLower x ≤ roundLower y := by
  unfold roundLower
  have hf : ⌊x*gridScale⌋ ≤ ⌊y*gridScale⌋ :=
    Int.floor_mono (mul_le_mul_of_nonneg_right h (by norm_num [gridScale]))
  exact div_le_div_of_nonneg_right (by exact_mod_cast hf)
    (by norm_num [gridScale])

private theorem roundUpper_mono {x y : ℚ} (h : x ≤ y) :
    roundUpper x ≤ roundUpper y := by
  unfold roundUpper
  have hf : ⌊x*gridScale⌋ ≤ ⌊y*gridScale⌋ :=
    Int.floor_mono (mul_le_mul_of_nonneg_right h (by norm_num [gridScale]))
  apply div_le_div_of_nonneg_right _ (by norm_num [gridScale])
  have hf' : ⌊x*gridScale⌋ + 1 ≤ ⌊y*gridScale⌋ + 1 := by omega
  exact_mod_cast hf'

private theorem point_mul_neg_half (a : Box) (ha : a.lo ≤ a.hi) :
    (Box.point (-1/2)).mul a = ⟨(-1/2)*a.hi, (-1/2)*a.lo⟩ := by
  rcases a with ⟨lo, hi⟩
  have h : (-1/2:ℚ)*hi ≤ (-1/2)*lo :=
    mul_le_mul_of_nonpos_left ha (by norm_num)
  simp [Box.mul, Box.point, min_eq_right h, max_eq_left h]

private theorem ordered_of_contains {a : Box} {x : ℝ} (h : a.Contains x) :
    a.lo ≤ a.hi := by
  exact_mod_cast le_trans h.1 h.2

private theorem bmul_neg_half_subset {a b : Box} (h : a.Subset b)
    (ha : a.lo ≤ a.hi) (hb : b.lo ≤ b.hi) :
    (bmul (Box.point (-1/2)) a).Subset
      (bmul (Box.point (-1/2)) b) := by
  have hlo : (-1/2:ℚ)*b.hi ≤ (-1/2)*a.hi :=
    mul_le_mul_of_nonpos_left h.2 (by norm_num)
  have hhi : (-1/2:ℚ)*a.lo ≤ (-1/2)*b.lo :=
    mul_le_mul_of_nonpos_left h.1 (by norm_num)
  rw [bmul, bmul, point_mul_neg_half a ha, point_mul_neg_half b hb]
  exact ⟨roundLower_mono hlo, roundUpper_mono hhi⟩

theorem tight_sample_scaled_log_subset_old (n : Fin 265) (hn : n.val < 205) :
    (tightSampleScaledLogBox n).Subset
      (bmul (Box.point (-1/2)) (sampleLogReference ⟨n.val, hn⟩)) := by
  let k : Fin 205 := ⟨n.val, hn⟩
  apply bmul_neg_half_subset
    (by simpa [tightSampleLogBox, hn, k] using sample_log_evaluator_check k)
  · exact ordered_of_contains (tight_sample_log_contains n)
  · exact_mod_cast le_trans (sample_log_reference_contains k).1
      (sample_log_reference_contains k).2

theorem tight_sample_scaled_log_range (n : Fin 265) :
    -4 ≤ (tightSampleScaledLogBox n).lo ∧
      (tightSampleScaledLogBox n).hi ≤ 4 := by
  by_cases hn : n.val < 205
  · let k : Fin 205 := ⟨n.val, hn⟩
    have h := sample_amplitude_range_check k
    have hs := tight_sample_scaled_log_subset_old n hn
    exact ⟨h.1.trans hs.1, hs.2.trans h.2⟩
  · let k : Fin 60 := ⟨n.val-205, by omega⟩
    have he : tightSampleLogBox n = tightHighSampleLogBox k := by
      simp [tightSampleLogBox, hn, k]
    rw [tightSampleScaledLogBox, he]
    have hscale (m : Fin 60) :
        -4 ≤ (bmul (Box.point (-1/2)) (tightHighSampleLogBox m)).lo ∧
          (bmul (Box.point (-1/2)) (tightHighSampleLogBox m)).hi ≤ 4 := by
      fin_cases m <;> norm_num [bmul, Box.point, tightHighSampleLogBox,
        Box.mul, Box.round, roundLower, roundUpper, gridScale]
    exact hscale k

def tightSampleAmplitudeBox (n : Fin 265) : Box :=
  expBox (tightSampleScaledLogBox n)

theorem tight_sample_amplitude_contains (n : Fin 265) :
    (tightSampleAmplitudeBox n).Contains
      (Real.exp (-Real.log (n.val+1:ℕ)/2)) := by
  have hl := bmul_contains (Box.point_contains (-1/2))
    (tight_sample_log_contains n)
  have he : ((-1/2:ℚ):ℝ)*Real.log (n.val+1:ℕ) =
      -Real.log (n.val+1:ℕ)/2 := by norm_num; ring
  rw [he] at hl
  exact exp_box hl (tight_sample_scaled_log_range n).1
    (tight_sample_scaled_log_range n).2

def tightSampleJetBox (n : Fin 265) (r : ℕ) : Box :=
  bmul (tightSampleAmplitudeBox n)
    (bmul (bpow (bneg (tightSampleLogBox n)) r)
      (Box.point ((r.factorial:ℚ)⁻¹)))

theorem tight_sample_jet_box (n : Fin 265) (r : ℕ) :
    (tightSampleJetBox n r).Contains (sampleRealJet (n.val+1) r) := by
  have h := bmul_contains (tight_sample_amplitude_contains n)
    (bmul_contains
      (bpow_contains (Box.neg_contains (tight_sample_log_contains n)) r)
      (Box.point_contains ((r.factorial:ℚ)⁻¹)))
  simpa only [tightSampleJetBox, bneg, sampleRealJet, div_eq_mul_inv,
    Rat.cast_inv, Rat.cast_natCast, mul_assoc] using h

def tightHead80JetBox (r : ℕ) : Box :=
  badd (badd (Box.point (if r=0 then 1 else 0))
    (bsumFin (fun m : Fin 80 =>
      badd (bsub (tightSampleJetBox ⟨3*m.val+1, by omega⟩ r)
        (bmul (Box.point 2) (tightSampleJetBox ⟨3*m.val+2, by omega⟩ r)))
        (tightSampleJetBox ⟨3*m.val+3, by omega⟩ r))))
    (bsumFin (fun k : Fin 24 =>
      bmul (Box.point (boundary48Weight k))
        (tightSampleJetBox ⟨241+k.val, by omega⟩ r)))

def head80RealJet (r : ℕ) : ℝ :=
  (if r=0 then 1 else 0) +
    (∑ m ∈ Finset.range 80,
      (sampleRealJet (3*m+2) r - 2*sampleRealJet (3*m+3) r +
        sampleRealJet (3*m+4) r)) +
    ∑ k : Fin 24, (boundary48Weight k : ℝ)*sampleRealJet (242+k.val) r

theorem tight_head80_jet_box (r : ℕ) :
    (tightHead80JetBox r).Contains (head80RealJet r) := by
  have hcell (m : Fin 80) :
      (badd (bsub (tightSampleJetBox ⟨3*m.val+1, by omega⟩ r)
        (bmul (Box.point 2) (tightSampleJetBox ⟨3*m.val+2, by omega⟩ r)))
        (tightSampleJetBox ⟨3*m.val+3, by omega⟩ r)).Contains
        (sampleRealJet (3*m.val+2) r - 2*sampleRealJet (3*m.val+3) r +
          sampleRealJet (3*m.val+4) r) := by
    have h1 : 3*m.val+1+1=3*m.val+2 := by omega
    have h2 : 3*m.val+2+1=3*m.val+3 := by omega
    have h3 : 3*m.val+3+1=3*m.val+4 := by omega
    simpa only [Fin.val_mk, h1, h2, h3, Rat.cast_ofNat] using badd_contains
      (bsub_contains (tight_sample_jet_box ⟨3*m.val+1, by omega⟩ r)
        (bmul_contains (Box.point_contains 2)
          (tight_sample_jet_box ⟨3*m.val+2, by omega⟩ r)))
      (tight_sample_jet_box ⟨3*m.val+3, by omega⟩ r)
  have hb (k : Fin 24) :
      (bmul (Box.point (boundary48Weight k))
        (tightSampleJetBox ⟨241+k.val, by omega⟩ r)).Contains
        ((boundary48Weight k:ℝ)*sampleRealJet (242+k.val) r) := by
    have h : 241+k.val+1=242+k.val := by omega
    simpa only [Fin.val_mk, h] using
      bmul_contains (Box.point_contains (boundary48Weight k))
        (tight_sample_jet_box ⟨241+k.val, by omega⟩ r)
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
  simpa only [tightHead80JetBox, head80RealJet, Rat.cast_ofNat,
    apply_ite, Rat.cast_one, Rat.cast_zero] using hh

#print axioms tight_sample_log_contains
#print axioms tight_sample_jet_box
#print axioms tight_head80_jet_box

end
end C3ShiftedFourth
