import CompletionPrimitiveBoxes
import ElementaryJetFormula

namespace CarryC3Boxes
open CarryC3Tail CarryC3Gamma
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3000000

def bsumFin {N : ℕ} (a : Fin N → Box) : Box :=
  bsum (fun k => if hk : k<N then a ⟨k,hk⟩ else Box.point 0) N

theorem bsumFin_contains {N : ℕ} (a : Fin N → Box) (f : Fin N → ℝ)
    (h : ∀ j, (a j).Contains (f j)) : (bsumFin a).Contains (∑ j : Fin N, f j) := by
  have hh := bsum_contains N
    (fun k => if hk : k<N then a ⟨k,hk⟩ else Box.point 0)
    (fun k => if hk : k<N then f ⟨k,hk⟩ else 0) (by intro k hk; simpa only [dif_pos hk] using h ⟨k,hk⟩)
  have he : (∑ j : Fin N, f j)=∑ k ∈ Finset.range N, if hk:k<N then f ⟨k,hk⟩ else 0 := by
    exact Finset.sum_fin_eq_sum_range f
  rw [he]
  exact hh

def sampleJetBox (n : Fin 205) (r : ℕ) : Box :=
  bmul (sampleAmplitudeReference n)
    (bmul (bpow (bneg (sampleLogReference n)) r) (Box.point ((r.factorial:ℚ)⁻¹)))

theorem sample_jet_box (n : Fin 205) (r : ℕ) :
    (sampleJetBox n r).Contains (sampleRealJet (n.val+1) r) := by
  have h := bmul_contains (sample_amplitude_reference_contains n)
    (bmul_contains (bpow_contains (Box.neg_contains (sample_log_reference_contains n)) r)
      (Box.point_contains ((r.factorial:ℚ)⁻¹)))
  simpa only [sampleJetBox,bneg,sampleRealJet,div_eq_mul_inv,Rat.cast_inv,Rat.cast_natCast,mul_assoc] using h

def headJetBox (r : ℕ) : Box :=
  badd (badd (Box.point (if r=0 then 1 else 0))
    (bsumFin (fun m : Fin 64 =>
      badd (bsub (sampleJetBox ⟨3*m.val+1,by omega⟩ r)
        (bmul (Box.point 2) (sampleJetBox ⟨3*m.val+2,by omega⟩ r)))
        (sampleJetBox ⟨3*m.val+3,by omega⟩ r))))
    (bsumFin (fun k : Fin 12 => bmul (Box.point (boundaryWeight k))
      (sampleJetBox ⟨193+k.val,by omega⟩ r)))

theorem head_jet_box (r : ℕ) : (headJetBox r).Contains (headRealJet 64 r) := by
  have hcell (m : Fin 64) := badd_contains
    (bsub_contains (sample_jet_box ⟨3*m.val+1,by omega⟩ r)
      (bmul_contains (Box.point_contains 2) (sample_jet_box ⟨3*m.val+2,by omega⟩ r)))
    (sample_jet_box ⟨3*m.val+3,by omega⟩ r)
  have hb (k : Fin 12) := bmul_contains (Box.point_contains (boundaryWeight k))
    (sample_jet_box ⟨193+k.val,by omega⟩ r)
  have hh := badd_contains (badd_contains (Box.point_contains (if r=0 then 1 else 0))
    (bsumFin_contains _ _ hcell)) (bsumFin_contains _ _ hb)
  have he : (∑ m : Fin 64, (sampleRealJet (3*m.val+1+1) r-
      (2:ℝ)*sampleRealJet (3*m.val+2+1) r+sampleRealJet (3*m.val+3+1) r))=
      ∑ m ∈ Finset.range 64, (sampleRealJet (3*m+2) r-2*sampleRealJet (3*m+3) r+sampleRealJet (3*m+4) r) := by
    simpa only [Nat.add_assoc] using Fin.sum_univ_eq_sum_range
      (fun m : ℕ => sampleRealJet (3*m+2) r-2*sampleRealJet (3*m+3) r+sampleRealJet (3*m+4) r) 64
  simp only [show ∀ k : Fin 12, 193+k.val+1=3*64+2+k.val by intro k; omega] at hh
  norm_num only [Rat.cast_ofNat] at hh
  rw [he] at hh
  simpa only [headRealJet,headJetBox,Rat.cast_ofNat,apply_ite,Rat.cast_one,Rat.cast_zero] using hh

def polynomialJetBox (r : ℕ) : Box := Box.point (if r=0 then -1/8 else if r=2 then 1/2 else 0)
def exponentialJetBox (r : ℕ) : Box := bmul
  piAmplitudeReference
  (bmul (bpow (bmul (Box.point (-1/2)) piLogReference) r) (Box.point ((r.factorial:ℚ)⁻¹)))
def chartJetBox (r : ℕ) : Box := bsub (Box.point (if r=0 then 1 else 0))
  (bmul chartAmplitudeReference
    (bmul (bpow (bneg logThreeBox) r) (Box.point ((r.factorial:ℚ)⁻¹))))

def convolutionBox (a b : ℕ → Box) (n : ℕ) : Box :=
  bsum (fun j => bmul (a j) (b (n-j))) (n+1)

theorem convolution_box (a b : ℕ → Box) (f g : ℕ → ℝ)
    (ha : ∀ j, (a j).Contains (f j)) (hb : ∀ j, (b j).Contains (g j)) (n : ℕ) :
    (convolutionBox a b n).Contains (convolution f g n) := by
  exact bsum_contains _ _ _ (fun j _ => bmul_contains (ha j) (hb (n-j)))

def reciprocalJetBox (c : ℕ → Box) : (n : ℕ) → Box
  | 0 => binv (c 0)
  | n+1 => bmul (bneg (bsumFin (fun j : Fin (n+1) =>
      bmul (reciprocalJetBox c j.val) (c (n+1-j.val))))) (binv (c 0))
termination_by n => n

theorem reciprocal_jet_box (c : ℕ → Box) (f : ℕ → ℝ)
    (hc : ∀ j, (c j).Contains (f j)) (h0 : 0<(c 0).lo ∨ (c 0).hi<0) (n : ℕ) :
    (reciprocalJetBox c n).Contains (reciprocalJet f n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simpa only [reciprocalJetBox,reciprocalJet] using binv_contains (hc 0) h0
    | succ n =>
      have hsum := bsumFin_contains
        (fun j : Fin (n+1) => bmul (reciprocalJetBox c j.val) (c (n+1-j.val)))
        (fun j : Fin (n+1) => reciprocalJet f j.val*f (n+1-j.val))
        (fun j => bmul_contains (ih j.val (by omega)) (hc _))
      simpa only [reciprocalJetBox,reciprocalJet,bneg,div_eq_mul_inv] using
        bmul_contains (Box.neg_contains hsum) (binv_contains (hc 0) h0)

def leftJetBox : ℕ → Box := convolutionBox
  (convolutionBox (convolutionBox polynomialJetBox exponentialJetBox) (reciprocalJetBox chartJetBox)) headJetBox

def completedJetBox (r : Fin 7) : Box :=
  bsumFin (fun j : Fin (r.val+1) => bmul (leftJetBox j.val)
    (Box.point (gammaRealReference ⟨r.val-j.val,by omega⟩)))

theorem polynomial_jet_box (r : ℕ) : (polynomialJetBox r).Contains (polynomialRealJet r) := by
  unfold polynomialJetBox polynomialRealJet
  split_ifs <;> norm_num [Box.Contains,Box.point]

theorem exponential_jet_box (r : ℕ) : (exponentialJetBox r).Contains (exponentialRealJet r) := by
  have hl := bmul_contains (Box.point_contains (-1/2)) pi_log_reference_contains
  have he : ((-1/2:ℚ):ℝ)*Real.log Real.pi = -Real.log Real.pi/2 := by norm_num; ring
  rw [he] at hl
  have h := bmul_contains pi_amplitude_reference_contains
    (bmul_contains (bpow_contains hl r) (Box.point_contains ((r.factorial:ℚ)⁻¹)))
  simpa only [exponentialJetBox,exponentialRealJet,div_eq_mul_inv,Rat.cast_inv,Rat.cast_natCast,mul_assoc] using h

theorem chart_jet_box (r : ℕ) : (chartJetBox r).Contains (chartRealJet r) := by
  have h := bsub_contains (Box.point_contains (if r=0 then 1 else 0))
    (bmul_contains chart_amplitude_reference_contains
      (bmul_contains (bpow_contains (Box.neg_contains log_three_reference_contains) r)
        (Box.point_contains ((r.factorial:ℚ)⁻¹))))
  simpa only [chartJetBox,chartRealJet,bneg,div_eq_mul_inv,Rat.cast_inv,Rat.cast_natCast,
    apply_ite,Rat.cast_one,Rat.cast_zero,mul_assoc] using h

theorem chart_center_interval_negative : (chartJetBox 0).hi < 0 := by decide +kernel

theorem left_jet_box (r : ℕ) : (leftJetBox r).Contains (leftRealJet r) :=
  convolution_box _ _ _ _ (convolution_box _ _ _ _
    (convolution_box _ _ _ _ polynomial_jet_box exponential_jet_box)
    (reciprocal_jet_box chartJetBox chartRealJet chart_jet_box (Or.inr chart_center_interval_negative))) head_jet_box r

theorem completed_jet_box (r : Fin 7) :
    (completedJetBox r).Contains (finiteCompletedRealJet r) := by
  have hh := bsumFin_contains
    (fun j : Fin (r.val+1) => bmul (leftJetBox j.val) (Box.point (gammaRealReference ⟨r.val-j.val,by omega⟩)))
    (fun j : Fin (r.val+1) => leftRealJet j.val*(gammaRealReference ⟨r.val-j.val,by omega⟩:ℝ))
    (fun j => bmul_contains (left_jet_box j.val) (Box.point_contains _))
  have he : (∑ j : Fin (r.val+1), leftRealJet j.val*(gammaRealReference ⟨r.val-j.val,by omega⟩:ℝ))=
      finiteCompletedRealJet r := by
    unfold finiteCompletedRealJet
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.mem_range.mp hj,dif_pos]
  rw [he] at hh
  exact hh

end CarryC3Boxes
