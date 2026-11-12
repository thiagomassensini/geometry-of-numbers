import GammaThirteen
import FiniteCoefficientBoxes

namespace CarryC3Boxes
open CarryC3Tail CarryC3Gamma
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 15000000
set_option maxRecDepth 30000

def cachedHead48JetBox (r : ℕ) : Box :=
  if hr : r < 13 then head48ReferenceBox ⟨r, hr⟩ else head48JetBox r

theorem cached_head48_jet_contains (r : ℕ) :
    (cachedHead48JetBox r).Contains (head48RealJet r) := by
  unfold cachedHead48JetBox
  split_ifs with hr
  · exact head48_reference_contains ⟨r, hr⟩
  · exact head48_jet_box r

def logThreeBoxTight : Box :=
  ⟨logReferenceTight-1/10^44, logReferenceTight+1/10^44⟩

theorem log_three_tight_contains :
    logThreeBoxTight.Contains (Real.log 3) := by
  have h := log_three_tight_box
  change ((logReferenceTight-(1/10^44:ℚ):ℚ):ℝ) ≤ Real.log 3 ∧
    Real.log 3 ≤ ((logReferenceTight+(1/10^44:ℚ):ℚ):ℝ)
  push_cast
  rw [abs_le] at h
  constructor <;> linarith

def chartAmplitudeReferenceTight : Box :=
  ⟨173205080756887729352744634150587236694280525381038/10^50,
    173205080756887729352744634150587236694280525381039/10^50⟩

theorem chart_amplitude_tight_contains :
    chartAmplitudeReferenceTight.Contains (Real.exp (Real.log 3/2)) := by
  have he : Real.exp (Real.log 3/2) = Real.sqrt 3 := by
    symm
    apply (Real.sqrt_eq_iff_mul_self_eq (by norm_num) (Real.exp_pos _).le).2
    rw [← Real.exp_add, show Real.log 3/2+Real.log 3/2=Real.log 3 by ring,
      Real.exp_log (by norm_num : (0:ℝ)<3)]
  rw [he]
  constructor
  · have hs : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
    have hl : ((173205080756887729352744634150587236694280525381038/10^50:ℚ):ℝ)^2 ≤ 3 := by
      norm_num
    have hp : 0 ≤ ((173205080756887729352744634150587236694280525381038/10^50:ℚ):ℝ) := by norm_num
    by_contra hn
    have hlt : Real.sqrt 3 <
        ((173205080756887729352744634150587236694280525381038/10^50:ℚ):ℝ) := lt_of_not_ge hn
    have hdiff : 0 <
        ((173205080756887729352744634150587236694280525381038/10^50:ℚ):ℝ)-Real.sqrt 3 := sub_pos.mpr hlt
    have hsum : 0 <
        ((173205080756887729352744634150587236694280525381038/10^50:ℚ):ℝ)+Real.sqrt 3 := by positivity
    have hprod := mul_pos hdiff hsum
    have heq : ((173205080756887729352744634150587236694280525381038/10^50:ℚ):ℝ)^2-
        (Real.sqrt 3)^2 =
        (((173205080756887729352744634150587236694280525381038/10^50:ℚ):ℝ)-Real.sqrt 3)*
          (((173205080756887729352744634150587236694280525381038/10^50:ℚ):ℝ)+Real.sqrt 3) := by ring
    rw [← heq, hs] at hprod
    linarith
  · have hs : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
    have hu : 3 ≤ ((173205080756887729352744634150587236694280525381039/10^50:ℚ):ℝ)^2 := by
      norm_num
    have hp : 0 ≤ ((173205080756887729352744634150587236694280525381039/10^50:ℚ):ℝ) := by norm_num
    by_contra hn
    have hlt : ((173205080756887729352744634150587236694280525381039/10^50:ℚ):ℝ) < Real.sqrt 3 := lt_of_not_ge hn
    have hdiff : 0 < Real.sqrt 3-
        ((173205080756887729352744634150587236694280525381039/10^50:ℚ):ℝ) := sub_pos.mpr hlt
    have hsum : 0 < Real.sqrt 3+
        ((173205080756887729352744634150587236694280525381039/10^50:ℚ):ℝ) := by positivity
    have hprod := mul_pos hdiff hsum
    have heq : (Real.sqrt 3)^2-
        ((173205080756887729352744634150587236694280525381039/10^50:ℚ):ℝ)^2 =
        (Real.sqrt 3-((173205080756887729352744634150587236694280525381039/10^50:ℚ):ℝ))*
          (Real.sqrt 3+((173205080756887729352744634150587236694280525381039/10^50:ℚ):ℝ)) := by ring
    rw [← heq, hs] at hprod
    linarith

def chartJetBoxTight (r : ℕ) : Box := bsub (Box.point (if r=0 then 1 else 0))
  (bmul chartAmplitudeReferenceTight
    (bmul (bpow (bneg logThreeBoxTight) r) (Box.point ((r.factorial:ℚ)⁻¹))))

theorem chart_jet_box_tight (r : ℕ) :
    (chartJetBoxTight r).Contains (chartRealJet r) := by
  have h := bsub_contains (Box.point_contains (if r=0 then 1 else 0))
    (bmul_contains (chart_amplitude_tight_contains)
      (bmul_contains (bpow_contains (Box.neg_contains log_three_tight_contains) r)
        (Box.point_contains ((r.factorial:ℚ)⁻¹))))
  simpa only [chartJetBoxTight, chartRealJet, bneg, div_eq_mul_inv,
    Rat.cast_inv, Rat.cast_natCast, apply_ite, Rat.cast_one, Rat.cast_zero,
    mul_assoc] using h

theorem chart_center_interval_negative_tight : (chartJetBoxTight 0).hi<0 := by
  decide +kernel

def leftRealJet48 : ℕ → ℝ := convolution
  (convolution (convolution polynomialRealJet exponentialRealJet)
    (reciprocalJet chartRealJet)) head48RealJet

def leftJetBox48 : ℕ → Box := convolutionBox
  (convolutionBox (convolutionBox polynomialJetBox exponentialJetBox)
    (reciprocalJetBox chartJetBoxTight)) cachedHead48JetBox

theorem left_jet_box48 (r : ℕ) :
    (leftJetBox48 r).Contains (leftRealJet48 r) := by
  exact convolution_box _ _ _ _
    (convolution_box _ _ _ _
      (convolution_box _ _ _ _ polynomial_jet_box exponential_jet_box)
      (reciprocal_jet_box chartJetBoxTight chartRealJet chart_jet_box_tight
        (Or.inr chart_center_interval_negative_tight)))
    cached_head48_jet_contains r

def finiteCompletedRealJet48 (r : Fin 13) : ℝ :=
  ∑ j ∈ Finset.range (r.val+1),
    leftRealJet48 j * (gammaRealReference13 ⟨r.val-j, by omega⟩:ℝ)

def completedJetBox48 (r : Fin 13) : Box :=
  bsumFin (fun j : Fin (r.val+1) =>
    bmul (leftJetBox48 j.val)
      (Box.point (gammaRealReference13 ⟨r.val-j.val, by omega⟩)))

theorem completed_jet_box48 (r : Fin 13) :
    (completedJetBox48 r).Contains (finiteCompletedRealJet48 r) := by
  have hh := bsumFin_contains
    (fun j : Fin (r.val+1) => bmul (leftJetBox48 j.val)
      (Box.point (gammaRealReference13 ⟨r.val-j.val, by omega⟩)))
    (fun j : Fin (r.val+1) => leftRealJet48 j.val *
      (gammaRealReference13 ⟨r.val-j.val, by omega⟩:ℝ))
    (fun j => bmul_contains (left_jet_box48 j.val) (Box.point_contains _))
  have he : (∑ j : Fin (r.val+1), leftRealJet48 j.val *
      (gammaRealReference13 ⟨r.val-j.val, by omega⟩:ℝ)) =
      finiteCompletedRealJet48 r := by
    unfold finiteCompletedRealJet48
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.mem_range.mp hj, dif_pos]
  rw [he] at hh
  exact hh

def headCoefficientBox48 (j : Fin 7) : Box :=
  if j.val % 2 = 0 then completedJetBox48 ⟨2*j.val, by omega⟩
    else (completedJetBox48 ⟨2*j.val, by omega⟩).neg

def headCoefficientReal48 (j : Fin 7) : ℝ :=
  if j.val % 2 = 0 then finiteCompletedRealJet48 ⟨2*j.val, by omega⟩
    else -finiteCompletedRealJet48 ⟨2*j.val, by omega⟩

theorem head_coefficient_contains48 (j : Fin 7) :
    (headCoefficientBox48 j).Contains (headCoefficientReal48 j) := by
  unfold headCoefficientBox48 headCoefficientReal48
  split_ifs
  · exact completed_jet_box48 _
  · exact Box.neg_contains (completed_jet_box48 _)

/-- Exact interval operations are used here to avoid repeatedly rounding a
high-order reciprocal recurrence. The box endpoints themselves remain
rational; no numerical approximation is hidden in this evaluator. -/
def sumBoxFinExact {N : ℕ} (a : Fin N → Box) : Box :=
  ⟨∑ j : Fin N, (a j).lo, ∑ j : Fin N, (a j).hi⟩

theorem sumBoxFinExact_contains {N : ℕ} (a : Fin N → Box) (f : Fin N → ℝ)
    (h : ∀ j, (a j).Contains (f j)) :
    (sumBoxFinExact a).Contains (∑ j : Fin N, f j) := by
  constructor
  · change ((∑ j : Fin N, (a j).lo : ℚ):ℝ) ≤ ∑ j : Fin N, f j
    push_cast
    exact Finset.sum_le_sum (fun j _ => (h j).1)
  · change (∑ j : Fin N, f j) ≤ ((∑ j : Fin N, (a j).hi : ℚ):ℝ)
    push_cast
    exact Finset.sum_le_sum (fun j _ => (h j).2)

def powBoxExact (a : Box) : ℕ → Box
  | 0 => Box.point 1
  | n+1 => (powBoxExact a n).mul a

theorem powBoxExact_contains {a : Box} {x : ℝ} (h : a.Contains x) (n : ℕ) :
    (powBoxExact a n).Contains (x^n) := by
  induction n with
  | zero => simpa [powBoxExact] using Box.point_contains (1:ℚ)
  | succ n ih => simpa [powBoxExact, pow_succ] using Box.mul_contains ih h

def convolutionBoxExact (a b : ℕ → Box) (n : ℕ) : Box :=
  sumBoxFinExact (fun j : Fin (n+1) => (a j.val).mul (b (n-j.val)))

theorem convolutionBoxExact_contains (a b : ℕ → Box) (f g : ℕ → ℝ)
    (ha : ∀ j, (a j).Contains (f j)) (hb : ∀ j, (b j).Contains (g j))
    (n : ℕ) : (convolutionBoxExact a b n).Contains (convolution f g n) := by
  have h := sumBoxFinExact_contains
    (a := fun j : Fin (n+1) => (a j.val).mul (b (n-j.val)))
    (f := fun j : Fin (n+1) => f j.val*g (n-j.val))
    (fun j => Box.mul_contains (ha j.val) (hb (n-j.val)))
  have he : (∑ j : Fin (n+1), f j.val*g (n-j.val)) = convolution f g n := by
    unfold convolution
    exact Fin.sum_univ_eq_sum_range
      (fun j : ℕ => f j*g (n-j)) (n+1)
  rw [he] at h
  exact h

def chartJetBoxExact (r : ℕ) : Box :=
  (Box.point (if r=0 then 1 else 0)).sub
    (chartAmplitudeReferenceTight.mul
      ((powBoxExact (logThreeBoxTight.neg) r).mul
        (Box.point ((r.factorial:ℚ)⁻¹))))

theorem chart_jet_box_exact (r : ℕ) :
    (chartJetBoxExact r).Contains (chartRealJet r) := by
  have h := Box.sub_contains (Box.point_contains (if r=0 then 1 else 0))
    (Box.mul_contains chart_amplitude_tight_contains
      (Box.mul_contains
        (powBoxExact_contains (Box.neg_contains log_three_tight_contains) r)
        (Box.point_contains ((r.factorial:ℚ)⁻¹))))
  simpa only [chartJetBoxExact, chartRealJet, Box.neg, div_eq_mul_inv,
    Rat.cast_inv, Rat.cast_natCast, apply_ite, Rat.cast_one, Rat.cast_zero,
    mul_assoc] using h

theorem chart_center_interval_negative_exact : (chartJetBoxExact 0).hi < 0 := by
  decide +kernel

def reciprocalJetBoxExact (c : ℕ → Box) : ℕ → Box
  | 0 => (c 0).inv
  | n+1 => (sumBoxFinExact (fun j : Fin (n+1) =>
      (reciprocalJetBoxExact c j.val).mul (c (n+1-j.val)))).neg.mul ((c 0).inv)
termination_by n => n

theorem reciprocal_jet_box_exact (c : ℕ → Box) (f : ℕ → ℝ)
    (hc : ∀ j, (c j).Contains (f j)) (h0 : 0<(c 0).lo ∨ (c 0).hi<0)
    (n : ℕ) : (reciprocalJetBoxExact c n).Contains (reciprocalJet f n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simpa [reciprocalJetBoxExact, reciprocalJet] using
        Box.inv_contains (hc 0) h0
    | succ n =>
      have hsum := sumBoxFinExact_contains
        (fun j : Fin (n+1) =>
          (reciprocalJetBoxExact c j.val).mul (c (n+1-j.val)))
        (fun j : Fin (n+1) => reciprocalJet f j.val*f (n+1-j.val))
        (fun j => Box.mul_contains (ih j.val (by omega)) (hc _))
      rw [reciprocalJetBoxExact, reciprocalJet]
      simpa only [div_eq_mul_inv] using
        Box.mul_contains (Box.neg_contains hsum) (Box.inv_contains (hc 0) h0)

def exponentialJetBoxExact (r : ℕ) : Box :=
  piAmplitudeReference.mul
    ((powBoxExact ((Box.point (-1/2)).mul piLogReference) r).mul
      (Box.point ((r.factorial:ℚ)⁻¹)))

theorem exponential_jet_box_exact (r : ℕ) :
    (exponentialJetBoxExact r).Contains (exponentialRealJet r) := by
  have h := Box.mul_contains pi_amplitude_reference_contains
    (Box.mul_contains
      (powBoxExact_contains
        (Box.mul_contains (Box.point_contains (-1/2)) pi_log_reference_contains) r)
      (Box.point_contains ((r.factorial:ℚ)⁻¹)))
  have he : ((-1/2:ℚ):ℝ)*Real.log Real.pi=-Real.log Real.pi/2 := by
    norm_num
    ring
  rw [he] at h
  simpa only [exponentialJetBoxExact, exponentialRealJet, div_eq_mul_inv, Rat.cast_inv,
    Rat.cast_natCast, mul_assoc] using h

def leftJetBoxExact48 : ℕ → Box := convolutionBoxExact
  (convolutionBoxExact
    (convolutionBoxExact polynomialJetBox exponentialJetBoxExact)
    (reciprocalJetBoxExact chartJetBoxExact)) cachedHead48JetBox

theorem left_jet_box_exact48 (r : ℕ) :
    (leftJetBoxExact48 r).Contains (leftRealJet48 r) := by
  have h₁ (k : ℕ) := convolutionBoxExact_contains
    polynomialJetBox exponentialJetBoxExact polynomialRealJet exponentialRealJet
    polynomial_jet_box exponential_jet_box_exact k
  have h₂ (k : ℕ) := convolutionBoxExact_contains
    (convolutionBoxExact polynomialJetBox exponentialJetBoxExact)
    (reciprocalJetBoxExact chartJetBoxExact)
    (convolution polynomialRealJet exponentialRealJet) (reciprocalJet chartRealJet)
    h₁ (reciprocal_jet_box_exact chartJetBoxExact chartRealJet
      chart_jet_box_exact (Or.inr chart_center_interval_negative_exact)) k
  exact convolutionBoxExact_contains
    (convolutionBoxExact
      (convolutionBoxExact polynomialJetBox exponentialJetBoxExact)
      (reciprocalJetBoxExact chartJetBoxExact))
    cachedHead48JetBox
    (convolution (convolution polynomialRealJet exponentialRealJet)
      (reciprocalJet chartRealJet)) head48RealJet
    h₂ cached_head48_jet_contains r

def completedJetBoxExact48 (r : Fin 13) : Box :=
  sumBoxFinExact (fun j : Fin (r.val+1) =>
    (leftJetBoxExact48 j.val).mul
      (Box.point (gammaRealReference13 ⟨r.val-j.val, by omega⟩)))

theorem completed_jet_box_exact48 (r : Fin 13) :
    (completedJetBoxExact48 r).Contains (finiteCompletedRealJet48 r) := by
  have h := sumBoxFinExact_contains
    (fun j : Fin (r.val+1) =>
      (leftJetBoxExact48 j.val).mul
        (Box.point (gammaRealReference13 ⟨r.val-j.val, by omega⟩)))
    (fun j : Fin (r.val+1) => leftRealJet48 j.val *
      (gammaRealReference13 ⟨r.val-j.val, by omega⟩:ℝ))
    (fun j => Box.mul_contains (left_jet_box_exact48 j.val) (Box.point_contains _))
  have he : (∑ j : Fin (r.val+1), leftRealJet48 j.val *
      (gammaRealReference13 ⟨r.val-j.val, by omega⟩:ℝ)) =
      finiteCompletedRealJet48 r := by
    unfold finiteCompletedRealJet48
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.mem_range.mp hj, dif_pos]
  rw [he] at h
  exact h

#print axioms chart_jet_box_exact
#print axioms reciprocal_jet_box_exact
#print axioms left_jet_box_exact48
#print axioms completed_jet_box_exact48

end
end CarryC3Boxes
