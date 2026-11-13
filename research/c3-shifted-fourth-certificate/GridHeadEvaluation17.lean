import GridArithmetic17
import FastHeadEvaluation17
import TightInputCertificates17

namespace C3ShiftedFourth

open CarryC3Boxes CarryC3Tail
open scoped BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 30000000
set_option maxRecDepth 30000

/-- Source amplitude boxes on the same 265 addresses, encoded on the fixed
integer grid. The first 205 entries are the existing certified table; the
remaining 60 are the exact M=80 `expBox` outputs checked in this research. -/
def gridM80AmplitudeBox (n : Fin 265) : GridBox :=
  GridBox.ofBox (tightM80AmplitudeBox n)

/-- Source logarithm boxes on the M=80 addresses, encoded without evaluating
the original rational interval arithmetic at every subsequent jet operation. -/
def gridM80LogBox (n : Fin 265) : GridBox :=
  GridBox.ofBox (tightM80LogBox n)

theorem grid_m80_amplitude_contains (n : Fin 265) :
    (gridM80AmplitudeBox n).toBox.Contains
      (Real.exp (-Real.log (n.val+1:ℕ)/2)) := by
  exact Box.subset_contains (grid_toBox_ofBox_contains (tightM80AmplitudeBox n))
    (tight_m80_amplitude_box_contains n)

theorem grid_m80_log_contains (n : Fin 265) :
    (gridM80LogBox n).toBox.Contains (Real.log (n.val+1:ℕ)) := by
  exact Box.subset_contains (grid_toBox_ofBox_contains (tightM80LogBox n))
    (tight_m80_log_box_contains n)

def gridRationalBox (q : ℚ) : GridBox := GridBox.ofBox (Box.point q)

theorem grid_rational_box_contains (q : ℚ) :
    (gridRationalBox q).toBox.Contains (q:ℝ) := by
  exact Box.subset_contains (grid_toBox_ofBox_contains (Box.point q))
    (Box.point_contains q)

def gridM80SampleJetBox (n : Fin 265) (r : ℕ) : GridBox :=
  gscale (gmul (gridM80AmplitudeBox n)
    (gpow (gneg (gridM80LogBox n)) r)) ((r.factorial:ℚ)⁻¹)

theorem grid_m80_sample_jet_box (n : Fin 265) (r : ℕ) :
    (gridM80SampleJetBox n r).toBox.Contains (sampleRealJet (n.val+1) r) := by
  have h := bmul_contains
    (bmul_contains (grid_m80_amplitude_contains n)
      (bpow_contains (Box.neg_contains (grid_m80_log_contains n)) r))
    (Box.point_contains ((r.factorial:ℚ)⁻¹))
  change (gscale (gmul (gridM80AmplitudeBox n)
    (gpow (gneg (gridM80LogBox n)) r)) ((r.factorial:ℚ)⁻¹)).toBox.Contains _
  rw [grid_toBox_gscale, grid_toBox_gmul, grid_toBox_gpow, grid_toBox_gneg]
  simpa only [gridM80SampleJetBox, sampleRealJet, div_eq_mul_inv,
    Rat.cast_inv, Rat.cast_natCast, mul_assoc, bneg] using h

def gridHead80JetBoxFrom (samples : Fin 265 → GridBox) (r : ℕ) : GridBox :=
  gadd (gadd (gpoint (if r=0 then 1 else 0))
    (gbsumFin (fun m : Fin 80 =>
      gadd (gsub (samples ⟨3*m.val+1, by omega⟩)
        (gmul (gpoint 2) (samples ⟨3*m.val+2, by omega⟩)))
        (samples ⟨3*m.val+3, by omega⟩))))
    (gbsumFin (fun k : Fin 24 =>
      gmul (GridBox.ofBox (Box.point (boundary48Weight k)))
        (samples ⟨241+k.val, by omega⟩)))

def gridHead80JetBox (r : ℕ) : GridBox :=
  gridHead80JetBoxFrom (fun n => gridM80SampleJetBox n r) r

theorem grid_head80_jet_box_from (samples : Fin 265 → GridBox) (r : ℕ)
    (hsamples : ∀ n, (samples n).toBox.Contains (sampleRealJet (n.val+1) r)) :
    (gridHead80JetBoxFrom samples r).toBox.Contains (head80RealJet r) := by
  have hcell (m : Fin 80) :
      (badd (bsub (samples ⟨3*m.val+1, by omega⟩).toBox
        (bmul (Box.point 2) (samples ⟨3*m.val+2, by omega⟩).toBox))
        (samples ⟨3*m.val+3, by omega⟩).toBox).Contains
        (sampleRealJet (3*m.val+2) r-2*sampleRealJet (3*m.val+3) r+
          sampleRealJet (3*m.val+4) r) := by
    have h1 : 3*m.val+1+1=3*m.val+2 := by omega
    have h2 : 3*m.val+2+1=3*m.val+3 := by omega
    have h3 : 3*m.val+3+1=3*m.val+4 := by omega
    simpa only [Fin.val_mk, h1, h2, h3, Rat.cast_ofNat] using badd_contains
      (bsub_contains (hsamples ⟨3*m.val+1, by omega⟩)
        (bmul_contains (Box.point_contains 2)
          (hsamples ⟨3*m.val+2, by omega⟩)))
      (hsamples ⟨3*m.val+3, by omega⟩)
  have hb (k : Fin 24) :
      (bmul (gridRationalBox (boundary48Weight k)).toBox
        (samples ⟨241+k.val, by omega⟩).toBox).Contains
        ((boundary48Weight k:ℝ)*sampleRealJet (242+k.val) r) := by
    have haddr : 241+k.val+1=242+k.val := by omega
    exact bmul_contains (grid_rational_box_contains (boundary48Weight k))
      (by simpa only [haddr] using
        hsamples ⟨241+k.val, by omega⟩)
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
  convert hh using 1
  · simp only [gridHead80JetBoxFrom, gridRationalBox, grid_toBox_gadd,
      grid_toBox_gsub, grid_toBox_gmul, grid_toBox_gpoint,
      grid_toBox_gbsumFin, Int.cast_ite, Int.cast_one, Int.cast_zero]
    norm_num
  · simp [head80RealJet, apply_ite]

theorem grid_head80_jet_box (r : ℕ) :
    (gridHead80JetBox r).toBox.Contains (head80RealJet r) := by
  exact grid_head80_jet_box_from (fun n => gridM80SampleJetBox n r) r
    (fun n => grid_m80_sample_jet_box n r)

end
end C3ShiftedFourth
