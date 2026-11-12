import C3Head48Jet
import HeadEvaluatorData

namespace CarryC3Boxes
open CarryC3Tail
open scoped BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 20000

/-- Rational propagation of the 48 original bracket cells and the verified
24-point boundary. Every primitive sample is from the existing C3 boxes. -/
def head48JetBox (r : ℕ) : Box :=
  badd (badd (Box.point (if r = 0 then 1 else 0))
    (bsumFin (fun m : Fin 48 =>
      badd (bsub (sampleJetBox ⟨3*m.val+1, by omega⟩ r)
        (bmul (Box.point 2) (sampleJetBox ⟨3*m.val+2, by omega⟩ r)))
        (sampleJetBox ⟨3*m.val+3, by omega⟩ r))))
    (bsumFin (fun k : Fin 24 =>
      bmul (Box.point (boundary48Weight k))
        (sampleJetBox ⟨145+k.val, by omega⟩ r)))

theorem head48_jet_box (r : ℕ) :
    (head48JetBox r).Contains (head48RealJet r) := by
  have hcell (m : Fin 48) :
      (badd (bsub (sampleJetBox ⟨3*m.val+1, by omega⟩ r)
        (bmul (Box.point 2) (sampleJetBox ⟨3*m.val+2, by omega⟩ r)))
        (sampleJetBox ⟨3*m.val+3, by omega⟩ r)).Contains
        (sampleRealJet (3*m.val+2) r-2*sampleRealJet (3*m.val+3) r+
          sampleRealJet (3*m.val+4) r) := by
    have h1 : 3*m.val+1+1=3*m.val+2 := by omega
    have h2 : 3*m.val+2+1=3*m.val+3 := by omega
    have h3 : 3*m.val+3+1=3*m.val+4 := by omega
    simpa only [Fin.val_mk, h1, h2, h3, Rat.cast_ofNat] using badd_contains
      (bsub_contains (sample_jet_box ⟨3*m.val+1, by omega⟩ r)
        (bmul_contains (Box.point_contains 2)
          (sample_jet_box ⟨3*m.val+2, by omega⟩ r)))
      (sample_jet_box ⟨3*m.val+3, by omega⟩ r)
  have hb (k : Fin 24) :
      (bmul (Box.point (boundary48Weight k))
        (sampleJetBox ⟨145+k.val, by omega⟩ r)).Contains
        ((boundary48Weight k:ℝ)*sampleRealJet (146+k.val) r) := by
    have h : 145+k.val+1=146+k.val := by omega
    simpa only [Fin.val_mk, h] using bmul_contains (Box.point_contains (boundary48Weight k))
      (sample_jet_box ⟨145+k.val, by omega⟩ r)
  have hh := badd_contains
    (badd_contains (Box.point_contains (if r=0 then 1 else 0))
      (bsumFin_contains _ _ hcell))
    (bsumFin_contains _ _ hb)
  have he : (∑ m : Fin 48,
      (sampleRealJet (3*m.val+2) r-(2:ℝ)*sampleRealJet (3*m.val+3) r+
        sampleRealJet (3*m.val+4) r)) =
      ∑ m ∈ Finset.range 48,
        (sampleRealJet (3*m+2) r-2*sampleRealJet (3*m+3) r+
          sampleRealJet (3*m+4) r) := by
    exact Fin.sum_univ_eq_sum_range
      (fun m : ℕ => sampleRealJet (3*m+2) r-2*sampleRealJet (3*m+3) r+
        sampleRealJet (3*m+4) r) 48
  rw [he] at hh
  simpa only [head48JetBox, head48RealJet, Rat.cast_ofNat, apply_ite,
    Rat.cast_one, Rat.cast_zero] using hh

/-- Tight rational reference intervals for the 13 jets of the exact M=48
head. These are interval targets; inclusion is proved below by Lean. -/
def head48ReferenceBox (r : Fin 13) : Box := ![
  ⟨(10690536975109091562737/10000000000000000000000),
    (10690536975109091562753/10000000000000000000000)⟩,
  ⟨(231843338733349772253/2500000000000000000000),
    (463686677466699544541/5000000000000000000000)⟩,
  ⟨(-783175921189920265237/10000000000000000000000),
    (-783175921189920265077/10000000000000000000000)⟩,
  ⟨(236008935162572500229/10000000000000000000000),
    (118004467581286250241/5000000000000000000000)⟩,
  ⟨(-27477217744308116983/10000000000000000000000),
    (-13738608872154058341/5000000000000000000000)⟩,
  ⟨(-3925881657487702783/10000000000000000000000),
    (-1962940828743851247/5000000000000000000000)⟩,
  ⟨(2277045297717024737/10000000000000000000000),
    (227704529771702497/1000000000000000000000)⟩,
  ⟨(-46942552577446953/1000000000000000000000),
    (-469425525774469367/10000000000000000000000)⟩,
  ⟨(50413365580929133/10000000000000000000000),
    (50413365580929233/10000000000000000000000)⟩,
  ⟨(23515452712591/10000000000000000000000),
    (11757726356323/5000000000000000000000)⟩,
  ⟨(-1141131451748499/10000000000000000000000),
    (-142641431468559/1250000000000000000000)⟩,
  ⟨(12394326315909/500000000000000000000),
    (247886526318193/10000000000000000000000)⟩,
  ⟨(-31313954205877/10000000000000000000000),
    (-31313954205871/10000000000000000000000)⟩] r

theorem head48_evaluator_check (r : Fin 13) :
    (head48JetBox r.val).Subset (head48ReferenceBox r) := by
  fin_cases r <;> decide +kernel

theorem head48_reference_contains (r : Fin 13) :
    (head48ReferenceBox r).Contains (head48RealJet r.val) :=
  Box.subset_contains (head48_evaluator_check r) (head48_jet_box r.val)

#print axioms head48_jet_box
#print axioms head48_evaluator_check
#print axioms head48_reference_contains

end
end CarryC3Boxes
