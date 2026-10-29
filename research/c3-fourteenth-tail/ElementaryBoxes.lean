import RationalBoxes

namespace CarryC3Boxes
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 1024

def unitLogSum (a : ℚ) : ℚ := -∑ j ∈ Finset.range 128, (1-a)^(j+1)/(j+1)
def unitLogBox (a : ℚ) : Box := ((Box.point (unitLogSum a)).expand (1/10^35)).round

theorem unit_log_box (a : ℚ) (ha : 1/2 ≤ a) (ha1 : a ≤ 1) :
    (unitLogBox a).Contains (Real.log (a:ℝ)) := by
  have hl : (1/2:ℝ) ≤ (a:ℝ) := by
    simpa using (Rat.cast_le (K:=ℝ)).mpr ha
  have hu : (a:ℝ) ≤ 1 := by exact_mod_cast ha1
  have hx : |1-(a:ℝ)| < 1 := by rw [abs_of_nonneg (by linarith)]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hx 128
  rw [show 1-(1-(a:ℝ))=(a:ℝ) by ring,
    abs_of_nonneg (by linarith : (0:ℝ)≤1-(a:ℝ))] at h
  have hb : (1-(a:ℝ))^129/(1-(1-a)) ≤ (1/10^35:ℝ) := by
    have hp : (1-(a:ℝ))^129 ≤ (1/2:ℝ)^129 := pow_le_pow_left₀ (by linarith) (by linarith) _
    have hh := (div_le_div_of_nonneg_right hp (by linarith : (0:ℝ)≤1-(1-a))).trans
      (div_le_div_of_nonneg_left (by positivity : (0:ℝ)≤(1/2)^129)
        (by norm_num : (0:ℝ)<1/2) (by linarith : (1/2:ℝ)≤1-(1-a)))
    exact hh.trans (by norm_num)
  have he : |Real.log (a:ℝ)-(unitLogSum a:ℝ)| ≤ (1/10^35:ℝ) := by
    simpa [unitLogSum,sub_eq_add_neg,add_comm] using h.trans hb
  exact Box.round_contains (Box.expand_contains (Box.point_contains _) (by simpa using he))

def rationalLogBox (x : ℚ) (p : ℕ) : Box :=
  badd (bmul (Box.point p) (bneg (unitLogBox (1/2)))) (unitLogBox (x/2^p))

theorem rational_log_box (x : ℚ) (p : ℕ) (h : 1/2 ≤ x/2^p ∧ x/2^p ≤ 1) :
    (rationalLogBox x p).Contains (Real.log (x:ℝ)) := by
  have hx : 0 < x := by
    have hh := (le_div_iff₀ (by positivity : (0:ℚ)<2^p)).mp h.1
    have hp : (0:ℚ)<2^p := by positivity
    nlinarith
  have h2 := Box.neg_contains (unit_log_box (1/2) (by norm_num) (by norm_num))
  have he2 : -Real.log ((1/2:ℚ):ℝ) = Real.log 2 := by
    norm_num only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,one_div]
    rw [show (1/2:ℝ)=(2:ℝ)⁻¹ by norm_num,Real.log_inv,neg_neg]
  rw [he2] at h2
  have ht := badd_contains (bmul_contains (Box.point_contains (p:ℚ)) h2)
    (unit_log_box _ h.1 h.2)
  have he : (p:ℝ)*Real.log 2+Real.log ((x/2^p:ℚ):ℝ)=Real.log (x:ℝ) := by
    rw [Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat,Real.log_div
      (by exact_mod_cast hx.ne') (by positivity),Real.log_pow]
    ring
  simpa only [rationalLogBox,bneg,Rat.cast_natCast,he] using ht

def piLower : ℚ := 314159265358979323846/10^20
def piUpper : ℚ := 314159265358979323847/10^20
def piLogBox : Box := ⟨(rationalLogBox piLower 2).lo,(rationalLogBox piUpper 2).hi⟩

theorem pi_log_box : piLogBox.Contains (Real.log Real.pi) := by
  have hl := rational_log_box piLower 2 (by norm_num [piLower])
  have hu := rational_log_box piUpper 2 (by norm_num [piUpper])
  have hp : (0:ℝ)<(piLower:ℝ) := by norm_num [piLower]
  have hpl : (piLower:ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d20.le
    norm_num at h
    norm_num [piLower]
    exact h
  have hpu : Real.pi ≤ (piUpper:ℝ) := by
    have h := Real.pi_lt_d20.le
    norm_num at h
    norm_num [piUpper]
    exact h
  exact ⟨hl.1.trans (Real.log_le_log hp hpl),
    (Real.log_le_log Real.pi_pos hpu).trans hu.2⟩

def expBox (a : Box) : Box :=
  (bsum (fun k => bmul (bpow a k) (Box.point ((k.factorial:ℚ)⁻¹))) 64).expand (1/10^30)

theorem exp_polynomial_error (x : ℝ) (hx : |x| ≤ 4) :
    |Real.exp x-∑ k ∈ Finset.range 64, x^k/(k.factorial:ℝ)| ≤ (1/10^30:ℝ) := by
  have h := Complex.exp_bound' (x:=(x:ℂ)) (n:=64) (by
    rw [Complex.norm_real,Real.norm_eq_abs]
    exact (div_le_div_of_nonneg_right hx (by norm_num : (0:ℝ)≤65)).trans (by norm_num))
  have hb : ‖(x:ℂ)‖^64/(Nat.factorial 64:ℝ)*2 ≤ (1/10^30:ℝ) := by
    rw [Complex.norm_real,Real.norm_eq_abs]
    calc
      _ ≤ (4:ℝ)^64/(Nat.factorial 64:ℝ)*2 := by gcongr
      _ ≤ _ := by norm_num
  have he : ((Real.exp x-∑ k ∈ Finset.range 64, x^k/(k.factorial:ℝ)):ℂ) =
      Complex.exp (x:ℂ)-∑ k ∈ Finset.range 64, (x:ℂ)^k/(k.factorial:ℂ) := by
    push_cast
    rfl
  have hh := h.trans hb
  rw [← he,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] at hh
  exact hh

theorem exp_box {a : Box} {x : ℝ} (ha : a.Contains x)
    (hl : -4 ≤ a.lo) (hu : a.hi ≤ 4) : (expBox a).Contains (Real.exp x) := by
  have hx : |x| ≤ 4 := by
    have hl' : (-4:ℝ)≤a.lo := by exact_mod_cast hl
    have hu' : (a.hi:ℝ)≤4 := by exact_mod_cast hu
    rw [abs_le]
    exact ⟨hl'.trans ha.1,ha.2.trans hu'⟩
  have ht : (bsum (fun k => bmul (bpow a k) (Box.point ((k.factorial:ℚ)⁻¹))) 64).Contains
      (∑ k ∈ Finset.range 64, x^k/(k.factorial:ℝ)) := by
    apply bsum_contains
    intro k hk
    simpa only [Rat.cast_inv,Rat.cast_natCast,div_eq_mul_inv] using
      bmul_contains (bpow_contains ha k) (Box.point_contains ((k.factorial:ℚ)⁻¹))
  exact Box.expand_contains ht (by simpa only [Rat.cast_div,Rat.cast_pow,Rat.cast_one,Rat.cast_ofNat] using exp_polynomial_error x hx)

end CarryC3Boxes
