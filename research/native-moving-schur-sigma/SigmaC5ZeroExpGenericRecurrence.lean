import SigmaC5ZeroExpStage6Certificate
import SigmaC5ZeroExpStagesCertificate

open CarrySigmaObstruction ZetaLean ZetaLean.ComplexInterval

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option exponentiation.threshold 1024

lemma interval_mul_nonneg_box_helper (lo hi : ℚ) (hlo : 0 ≤ lo)
    (hle : lo ≤ hi) :
    (Interval.mul { lo := lo, hi := hi, le := hle }
      { lo := lo, hi := hi, le := hle }).lo = lo ^ 2 := by
  have hhi : 0 ≤ hi := le_trans hlo hle
  have h1 : lo * lo ≤ lo * hi := mul_le_mul_of_nonneg_left hle hlo
  have h2 : hi * lo ≤ hi * hi := mul_le_mul_of_nonneg_left hle hhi
  have h3 : lo * lo ≤ hi * lo := by rw [mul_comm hi lo]; exact h1
  simp only [Interval.mul, min_eq_left h1, min_eq_left h2, min_eq_left h3,
    pow_two]

lemma interval_mul_nonneg_box_hi_helper (lo hi : ℚ) (hlo : 0 ≤ lo)
    (hle : lo ≤ hi) :
    (Interval.mul { lo := lo, hi := hi, le := hle }
      { lo := lo, hi := hi, le := hle }).hi = hi ^ 2 := by
  have hhi : 0 ≤ hi := le_trans hlo hle
  have h1 : lo * lo ≤ lo * hi := mul_le_mul_of_nonneg_left hle hlo
  have h2 : hi * lo ≤ hi * hi := mul_le_mul_of_nonneg_left hle hhi
  have h3 : lo * hi ≤ hi * hi := mul_le_mul_of_nonneg_right hle hhi
  simp only [Interval.mul]
  rw [show max (lo * lo) (lo * hi) = lo * hi from max_eq_right h1,
      show max (hi * lo) (hi * hi) = hi * hi from max_eq_right h2,
      show max (lo * hi) (hi * hi) = hi * hi from max_eq_right h3]
  simp only [pow_two]

lemma interval_mul_symm_box_helper (v : ℚ) (hv : 0 ≤ v) :
    (Interval.mul { lo := -v, hi := v, le := by linarith }
      { lo := -v, hi := v, le := by linarith }).lo = -(v ^ 2) ∧
    (Interval.mul { lo := -v, hi := v, le := by linarith }
      { lo := -v, hi := v, le := by linarith }).hi = v ^ 2 := by
  have hneg : -(v ^ 2) ≤ v ^ 2 := by nlinarith
  constructor
  · change min (min ((-v) * (-v)) ((-v) * v))
        (min (v * (-v)) (v * v)) = -(v ^ 2)
    ring_nf
    simp [min_eq_right hneg, min_eq_left hneg]
  · change max (max ((-v) * (-v)) ((-v) * v))
        (max (v * (-v)) (v * v)) = v ^ 2
    ring_nf
    simp [max_eq_left hneg, max_eq_right hneg]

lemma interval_mul_pos_symm_lo_helper (lo hi v : ℚ) (hlo : 0 ≤ lo)
    (hle : lo ≤ hi) (hv : 0 ≤ v) :
    (Interval.mul { lo := lo, hi := hi, le := hle }
      { lo := -v, hi := v, le := by linarith }).lo = -(hi * v) := by
  change min (min (lo * (-v)) (lo * v)) (min (hi * (-v)) (hi * v)) = _
  ring_nf
  have hloV : -(lo * v) ≤ lo * v := by nlinarith [mul_nonneg hlo hv]
  have hhiV : -(v * hi) ≤ v * hi := by nlinarith [mul_nonneg (le_trans hlo hle) hv]
  have horder : -(hi * v) ≤ -(lo * v) := by
    have := mul_le_mul_of_nonneg_right hle hv
    linarith
  have horder' : -(v * hi) ≤ -(lo * v) := by
    rw [mul_comm v hi]
    exact horder
  simp only [min_eq_left hloV, min_eq_left hhiV, min_eq_right horder']

lemma interval_mul_pos_symm_hi_helper (lo hi v : ℚ) (hlo : 0 ≤ lo)
    (hle : lo ≤ hi) (hv : 0 ≤ v) :
    (Interval.mul { lo := lo, hi := hi, le := hle }
      { lo := -v, hi := v, le := by linarith }).hi = hi * v := by
  change max (max (lo * (-v)) (lo * v)) (max (hi * (-v)) (hi * v)) = _
  ring_nf
  have hloV : -(lo * v) ≤ lo * v := by nlinarith [mul_nonneg hlo hv]
  have hhiV : -(v * hi) ≤ v * hi := by nlinarith [mul_nonneg (le_trans hlo hle) hv]
  have horder : lo * v ≤ hi * v := mul_le_mul_of_nonneg_right hle hv
  have horder' : lo * v ≤ v * hi := by
    calc
      lo * v ≤ hi * v := horder
      _ = v * hi := by ring
  simp only [max_eq_right hloV, max_eq_right hhiV, max_eq_right horder']

lemma interval_mul_symm_pos_lo_helper (lo hi v : ℚ) (hlo : 0 ≤ lo)
    (hle : lo ≤ hi) (hv : 0 ≤ v) :
    (Interval.mul { lo := -v, hi := v, le := by linarith }
      { lo := lo, hi := hi, le := hle }).lo = -(v * hi) := by
  change min (min ((-v) * lo) ((-v) * hi)) (min (v * lo) (v * hi)) = _
  ring_nf
  have hposLo : 0 ≤ v * lo := mul_nonneg hv hlo
  have horder : v * lo ≤ v * hi := mul_le_mul_of_nonneg_left hle hv
  have hnegPos : -(v * hi) ≤ v * lo := by linarith
  have horderNeg : -(v * hi) ≤ -(v * lo) := by linarith
  simp only [min_eq_right horderNeg, min_eq_left horder,
    min_eq_left hnegPos]

lemma interval_mul_symm_pos_hi_helper (lo hi v : ℚ) (hlo : 0 ≤ lo)
    (hle : lo ≤ hi) (hv : 0 ≤ v) :
    (Interval.mul { lo := -v, hi := v, le := by linarith }
      { lo := lo, hi := hi, le := hle }).hi = v * hi := by
  change max (max ((-v) * lo) ((-v) * hi)) (max (v * lo) (v * hi)) = _
  ring_nf
  have hposLo : 0 ≤ v * lo := mul_nonneg hv hlo
  have hposHi : 0 ≤ v * hi := mul_nonneg hv (le_trans hlo hle)
  have horder : v * lo ≤ v * hi := mul_le_mul_of_nonneg_left hle hv
  have horderNeg : -(v * hi) ≤ -(v * lo) := by linarith
  have hmax : -(v * lo) ≤ v * hi := by linarith
  simp only [max_eq_left horderNeg, max_eq_right horder,
    max_eq_right hmax]

def c5GenericGrid : ℚ := 2 ^ 896

def c5GenericBox (a b : ℕ) : ComplexInterval := {
  re := {
    lo := (c5GenericGrid - (a : ℚ)) / c5GenericGrid
    hi := (c5GenericGrid + (b : ℚ)) / c5GenericGrid
    le := by
      have hD : 0 < c5GenericGrid := by norm_num [c5GenericGrid]
      apply (div_le_div_iff_of_pos_right hD).2
      have ha : 0 ≤ (a : ℚ) := Nat.cast_nonneg _
      have hb : 0 ≤ (b : ℚ) := Nat.cast_nonneg _
      linarith
  }
  im := {
    lo := -((b : ℚ) / c5GenericGrid)
    hi := (b : ℚ) / c5GenericGrid
    le := by
      have hD : 0 < c5GenericGrid := by norm_num [c5GenericGrid]
      have hb : 0 ≤ (b : ℚ) := Nat.cast_nonneg _
      have hb' : 0 ≤ (b : ℚ) / c5GenericGrid := div_nonneg hb (le_of_lt hD)
      linarith
  }
}

def c5GenericBoxSquare (a b : ℕ) : ComplexInterval :=
  (c5GenericBox a b).mul (c5GenericBox a b)

lemma c5GenericBoxSquare_re_lo (a b : ℕ)
    (haD : (a : ℚ) < c5GenericGrid) :
    (c5GenericBoxSquare a b).re.lo =
      ((c5GenericGrid - (a : ℚ)) / c5GenericGrid) ^ 2 -
        ((b : ℚ) / c5GenericGrid) ^ 2 := by
  let lo := (c5GenericGrid - (a : ℚ)) / c5GenericGrid
  let hi := (c5GenericGrid + (b : ℚ)) / c5GenericGrid
  let v := (b : ℚ) / c5GenericGrid
  have hD : 0 < c5GenericGrid := by norm_num [c5GenericGrid]
  have hlo : 0 ≤ lo := div_nonneg (sub_nonneg.mpr (le_of_lt haD)) (le_of_lt hD)
  have hle : lo ≤ hi := by
    dsimp [lo, hi]
    apply (div_le_div_iff_of_pos_right hD).2
    have ha : 0 ≤ (a : ℚ) := Nat.cast_nonneg _
    have hb : 0 ≤ (b : ℚ) := Nat.cast_nonneg _
    linarith
  have hv : 0 ≤ v := div_nonneg (Nat.cast_nonneg _) (le_of_lt hD)
  have hre := interval_mul_nonneg_box_helper lo hi hlo hle
  have him := interval_mul_symm_box_helper v hv
  change (Interval.mul (c5GenericBox a b).re (c5GenericBox a b).re).lo +
      -((Interval.mul (c5GenericBox a b).im (c5GenericBox a b).im).hi) = _
  rw [show (c5GenericBox a b).re = { lo := lo, hi := hi, le := hle } by
        rfl,
      show (c5GenericBox a b).im = { lo := -v, hi := v, le := by linarith } by
        simp [c5GenericBox, v],
      hre, him.2]
  ring

lemma c5GenericBoxSquare_re_hi (a b : ℕ)
    (haD : (a : ℚ) < c5GenericGrid) :
    (c5GenericBoxSquare a b).re.hi =
      ((c5GenericGrid + (b : ℚ)) / c5GenericGrid) ^ 2 +
        ((b : ℚ) / c5GenericGrid) ^ 2 := by
  let lo := (c5GenericGrid - (a : ℚ)) / c5GenericGrid
  let hi := (c5GenericGrid + (b : ℚ)) / c5GenericGrid
  let v := (b : ℚ) / c5GenericGrid
  have hD : 0 < c5GenericGrid := by norm_num [c5GenericGrid]
  have hlo : 0 ≤ lo := div_nonneg (sub_nonneg.mpr (le_of_lt haD)) (le_of_lt hD)
  have hle : lo ≤ hi := by
    dsimp [lo, hi]
    apply (div_le_div_iff_of_pos_right hD).2
    have ha : 0 ≤ (a : ℚ) := Nat.cast_nonneg _
    have hb : 0 ≤ (b : ℚ) := Nat.cast_nonneg _
    linarith
  have hv : 0 ≤ v := div_nonneg (Nat.cast_nonneg _) (le_of_lt hD)
  have hre := interval_mul_nonneg_box_hi_helper lo hi hlo hle
  have him := interval_mul_symm_box_helper v hv
  change (Interval.mul (c5GenericBox a b).re (c5GenericBox a b).re).hi +
      -((Interval.mul (c5GenericBox a b).im (c5GenericBox a b).im).lo) = _
  rw [show (c5GenericBox a b).re = { lo := lo, hi := hi, le := hle } by
        rfl,
      show (c5GenericBox a b).im = { lo := -v, hi := v, le := by linarith } by
        simp [c5GenericBox, v],
      hre, him.1]
  ring

lemma c5GenericBoxSquare_im_lo (a b : ℕ)
    (haD : (a : ℚ) < c5GenericGrid) :
    (c5GenericBoxSquare a b).im.lo =
      -2 * ((c5GenericGrid + (b : ℚ)) / c5GenericGrid) *
        ((b : ℚ) / c5GenericGrid) := by
  let lo := (c5GenericGrid - (a : ℚ)) / c5GenericGrid
  let hi := (c5GenericGrid + (b : ℚ)) / c5GenericGrid
  let v := (b : ℚ) / c5GenericGrid
  have hD : 0 < c5GenericGrid := by norm_num [c5GenericGrid]
  have hlo : 0 ≤ lo := div_nonneg (sub_nonneg.mpr (le_of_lt haD)) (le_of_lt hD)
  have hle : lo ≤ hi := by
    dsimp [lo, hi]
    apply (div_le_div_iff_of_pos_right hD).2
    have ha : 0 ≤ (a : ℚ) := Nat.cast_nonneg _
    have hb : 0 ≤ (b : ℚ) := Nat.cast_nonneg _
    linarith
  have hv : 0 ≤ v := div_nonneg (Nat.cast_nonneg _) (le_of_lt hD)
  have him := interval_mul_symm_box_helper v hv
  change (Interval.mul (c5GenericBox a b).re (c5GenericBox a b).im).lo +
      (Interval.mul (c5GenericBox a b).im (c5GenericBox a b).re).lo = _
  rw [show (c5GenericBox a b).re = { lo := lo, hi := hi, le := hle } by
        rfl,
      show (c5GenericBox a b).im = { lo := -v, hi := v, le := by linarith } by
        simp [c5GenericBox, v]]
  rw [interval_mul_pos_symm_lo_helper lo hi v hlo hle hv,
    interval_mul_symm_pos_lo_helper lo hi v hlo hle hv]
  ring

lemma c5GenericBoxSquare_im_hi (a b : ℕ)
    (haD : (a : ℚ) < c5GenericGrid) :
    (c5GenericBoxSquare a b).im.hi =
      2 * ((c5GenericGrid + (b : ℚ)) / c5GenericGrid) *
        ((b : ℚ) / c5GenericGrid) := by
  let lo := (c5GenericGrid - (a : ℚ)) / c5GenericGrid
  let hi := (c5GenericGrid + (b : ℚ)) / c5GenericGrid
  let v := (b : ℚ) / c5GenericGrid
  have hD : 0 < c5GenericGrid := by norm_num [c5GenericGrid]
  have hlo : 0 ≤ lo := div_nonneg (sub_nonneg.mpr (le_of_lt haD)) (le_of_lt hD)
  have hle : lo ≤ hi := by
    dsimp [lo, hi]
    apply (div_le_div_iff_of_pos_right hD).2
    have ha : 0 ≤ (a : ℚ) := Nat.cast_nonneg _
    have hb : 0 ≤ (b : ℚ) := Nat.cast_nonneg _
    linarith
  have hv : 0 ≤ v := div_nonneg (Nat.cast_nonneg _) (le_of_lt hD)
  change (Interval.mul (c5GenericBox a b).re (c5GenericBox a b).im).hi +
      (Interval.mul (c5GenericBox a b).im (c5GenericBox a b).re).hi = _
  rw [show (c5GenericBox a b).re = { lo := lo, hi := hi, le := hle } by
        rfl,
      show (c5GenericBox a b).im = { lo := -v, hi := v, le := by linarith } by
        rfl]
  rw [interval_mul_pos_symm_hi_helper lo hi v hlo hle hv,
    interval_mul_symm_pos_hi_helper lo hi v hlo hle hv]
  ring

lemma c5GenericBoxSquare_re_lo_floor (a b : ℕ)
    (hab : a < b) (haD : (a : ℚ) < c5GenericGrid)
    (h2bD : 2 * (b : ℚ) ^ 2 < c5GenericGrid) :
    Int.floor ((c5GenericBoxSquare a b).re.lo * 2 ^ 896) =
      (2 : ℤ) ^ 896 - 2 * (a : ℤ) - 1 := by
  have hD : 0 < c5GenericGrid := by norm_num [c5GenericGrid]
  have habQ : (a : ℚ) < (b : ℚ) := by exact_mod_cast hab
  have ha0 : 0 ≤ (a : ℚ) := Nat.cast_nonneg _
  have hb0 : 0 < (b : ℚ) := by linarith
  have hdelta : 0 < (b : ℚ) ^ 2 - (a : ℚ) ^ 2 := by
    have hprod : 0 < ((b : ℚ) - a) * ((b : ℚ) + a) :=
      mul_pos (sub_pos.mpr habQ) (by linarith)
    nlinarith [hprod]
  have hdeltaD : (b : ℚ) ^ 2 - (a : ℚ) ^ 2 < c5GenericGrid := by
    nlinarith [h2bD]
  have hdeltaLo : -1 < ((a : ℚ) ^ 2 - (b : ℚ) ^ 2) / c5GenericGrid := by
    rw [lt_div_iff₀ hD]
    nlinarith
  have hdeltaHi : ((a : ℚ) ^ 2 - (b : ℚ) ^ 2) / c5GenericGrid < 0 :=
    div_neg_of_neg_of_pos (by nlinarith) hD
  rw [c5GenericBoxSquare_re_lo a b haD]
  have hscale :
      (((c5GenericGrid - (a : ℚ)) / c5GenericGrid) ^ 2 -
        ((b : ℚ) / c5GenericGrid) ^ 2) * 2 ^ 896 =
      c5GenericGrid - 2 * (a : ℚ) +
        (((a : ℚ) ^ 2 - (b : ℚ) ^ 2) / c5GenericGrid) := by
    rw [show (2 : ℚ) ^ 896 = c5GenericGrid by rfl]
    field_simp [c5GenericGrid]
    ring_nf
  have htarget :
      (((2 : ℤ) ^ 896 - 2 * (a : ℤ) - 1 : ℤ) : ℚ) =
        c5GenericGrid - 2 * (a : ℚ) - 1 := by
    norm_num [c5GenericGrid]
  rw [hscale]
  apply Int.floor_eq_iff.mpr
  constructor
  · rw [htarget]
    linarith [hdeltaLo]
  · rw [htarget]
    linarith [hdeltaHi]

lemma c5GenericBoxSquare_re_hi_ceil (a b : ℕ)
    (hb : 0 < b) (haD : (a : ℚ) < c5GenericGrid)
    (h2bD : 2 * (b : ℚ) ^ 2 < c5GenericGrid) :
    Int.ceil ((c5GenericBoxSquare a b).re.hi * 2 ^ 896) =
      (2 : ℤ) ^ 896 + 2 * (b : ℤ) + 1 := by
  have hD : 0 < c5GenericGrid := by norm_num [c5GenericGrid]
  have hb0 : 0 < (b : ℚ) := by exact_mod_cast hb
  have h2bPos : 0 < 2 * (b : ℚ) ^ 2 := by positivity
  have hroundPos : 0 < (2 * (b : ℚ) ^ 2) / c5GenericGrid := div_pos h2bPos hD
  have hroundLt : (2 * (b : ℚ) ^ 2) / c5GenericGrid < 1 :=
    (div_lt_one hD).2 h2bD
  rw [c5GenericBoxSquare_re_hi a b haD]
  have hscale :
      (((c5GenericGrid + (b : ℚ)) / c5GenericGrid) ^ 2 +
        ((b : ℚ) / c5GenericGrid) ^ 2) * 2 ^ 896 =
      c5GenericGrid + 2 * (b : ℚ) +
        (2 * (b : ℚ) ^ 2) / c5GenericGrid := by
    rw [show (2 : ℚ) ^ 896 = c5GenericGrid by rfl]
    field_simp [c5GenericGrid]
    ring_nf
  have htarget :
      (((2 : ℤ) ^ 896 + 2 * (b : ℤ) + 1 : ℤ) : ℚ) =
        c5GenericGrid + 2 * (b : ℚ) + 1 := by
    norm_num [c5GenericGrid]
  rw [hscale]
  apply Int.ceil_eq_iff.mpr
  constructor
  · rw [htarget]
    linarith [hroundPos]
  · rw [htarget]
    linarith [hroundLt]

lemma c5GenericBoxSquare_im_lo_floor (a b : ℕ)
    (hb : 0 < b) (haD : (a : ℚ) < c5GenericGrid)
    (h2bD : 2 * (b : ℚ) ^ 2 < c5GenericGrid) :
    Int.floor ((c5GenericBoxSquare a b).im.lo * 2 ^ 896) =
      -2 * (b : ℤ) - 1 := by
  have hD : 0 < c5GenericGrid := by norm_num [c5GenericGrid]
  have hb0 : 0 < (b : ℚ) := by exact_mod_cast hb
  have h2bPos : 0 < 2 * (b : ℚ) ^ 2 := by positivity
  have hroundPos : 0 < (2 * (b : ℚ) ^ 2) / c5GenericGrid := div_pos h2bPos hD
  have hroundLt : (2 * (b : ℚ) ^ 2) / c5GenericGrid < 1 :=
    (div_lt_one hD).2 h2bD
  rw [c5GenericBoxSquare_im_lo a b haD]
  have hscale :
      (-2 * ((c5GenericGrid + (b : ℚ)) / c5GenericGrid) *
        ((b : ℚ) / c5GenericGrid)) * 2 ^ 896 =
      -2 * (b : ℚ) - (2 * (b : ℚ) ^ 2) / c5GenericGrid := by
    rw [show (2 : ℚ) ^ 896 = c5GenericGrid by rfl]
    field_simp [c5GenericGrid]
    ring_nf
  have htarget : (((-2 * (b : ℤ) - 1 : ℤ) : ℚ)) =
      -2 * (b : ℚ) - 1 := by norm_num
  rw [hscale]
  apply Int.floor_eq_iff.mpr
  constructor
  · rw [htarget]
    linarith [hroundLt]
  · rw [htarget]
    linarith [hroundPos]

lemma c5GenericBoxSquare_im_hi_ceil (a b : ℕ)
    (hb : 0 < b) (haD : (a : ℚ) < c5GenericGrid)
    (h2bD : 2 * (b : ℚ) ^ 2 < c5GenericGrid) :
    Int.ceil ((c5GenericBoxSquare a b).im.hi * 2 ^ 896) =
      2 * (b : ℤ) + 1 := by
  have hD : 0 < c5GenericGrid := by norm_num [c5GenericGrid]
  have hb0 : 0 < (b : ℚ) := by exact_mod_cast hb
  have h2bPos : 0 < 2 * (b : ℚ) ^ 2 := by positivity
  have hroundPos : 0 < (2 * (b : ℚ) ^ 2) / c5GenericGrid := div_pos h2bPos hD
  have hroundLt : (2 * (b : ℚ) ^ 2) / c5GenericGrid < 1 :=
    (div_lt_one hD).2 h2bD
  rw [c5GenericBoxSquare_im_hi a b haD]
  have hscale :
      (2 * ((c5GenericGrid + (b : ℚ)) / c5GenericGrid) *
        ((b : ℚ) / c5GenericGrid)) * 2 ^ 896 =
      2 * (b : ℚ) + (2 * (b : ℚ) ^ 2) / c5GenericGrid := by
    rw [show (2 : ℚ) ^ 896 = c5GenericGrid by rfl]
    field_simp [c5GenericGrid]
  have htarget : (((2 * (b : ℤ) + 1 : ℤ) : ℚ)) =
      2 * (b : ℚ) + 1 := by norm_num
  rw [hscale]
  apply Int.ceil_eq_iff.mpr
  constructor
  · rw [htarget]
    linarith [hroundPos]
  · rw [htarget]
    linarith [hroundLt]

theorem c5GenericBox_square_coarsen (a b : ℕ)
    (hab : a < b) (haD : (a : ℚ) < c5GenericGrid)
    (h2bD : 2 * (b : ℚ) ^ 2 < c5GenericGrid) :
    (c5GenericBoxSquare a b).coarsen 896 =
      c5GenericBox (2 * a + 1) (2 * b + 1) := by
  have hb : 0 < b := by omega
  simp only [ComplexInterval.coarsen, c5GenericBox, ComplexInterval.mk.injEq,
    Interval.mk.injEq, Interval.coarsen]
  constructor
  · constructor
    · rw [c5GenericBoxSquare_re_lo_floor a b hab haD h2bD]
      norm_num [c5GenericGrid]
      all_goals ring
    · rw [c5GenericBoxSquare_re_hi_ceil a b hb haD h2bD]
      norm_num [c5GenericGrid]
      all_goals ring
  · constructor
    · rw [c5GenericBoxSquare_im_lo_floor a b hb haD h2bD]
      norm_num [c5GenericGrid]
      all_goals ring
    · rw [c5GenericBoxSquare_im_hi_ceil a b hb haD h2bD]
      norm_num [c5GenericGrid]

def c5GenericA (r : ℕ) : ℕ := 3 * 2 ^ r - 1

def c5GenericB (r : ℕ) : ℕ := 4 * 2 ^ r - 1

def c5GenericStageBox (r : ℕ) : ComplexInterval :=
  c5GenericBox (c5GenericA r) (c5GenericB r)

lemma c5GenericA_succ (r : ℕ) : c5GenericA (r + 1) = 2 * c5GenericA r + 1 := by
  simp only [c5GenericA]
  rw [show r + 1 = Nat.succ r by omega, pow_succ]
  have hp : 0 < 2 ^ r := pow_pos (by norm_num) _
  omega

lemma c5GenericB_succ (r : ℕ) : c5GenericB (r + 1) = 2 * c5GenericB r + 1 := by
  simp only [c5GenericB]
  rw [show r + 1 = Nat.succ r by omega, pow_succ]
  have hp : 0 < 2 ^ r := pow_pos (by norm_num) _
  omega

lemma c5GenericA_lt_B (r : ℕ) : c5GenericA r < c5GenericB r := by
  have hp : 0 < 2 ^ r := pow_pos (by norm_num) _
  simp only [c5GenericA, c5GenericB]
  omega

lemma c5Generic_stage_parameters_bound (r : ℕ) (hr : r ≤ 190) :
    c5GenericA r < 2 ^ 192 ∧ c5GenericB r < 2 ^ 192 := by
  have hp : 2 ^ r ≤ 2 ^ 190 := Nat.pow_le_pow_right (by omega) hr
  constructor <;> simp only [c5GenericA, c5GenericB] <;> omega

lemma c5GenericA_lt_grid (r : ℕ) (hr : r ≤ 190) :
    (c5GenericA r : ℚ) < c5GenericGrid := by
  have hA := (c5Generic_stage_parameters_bound r hr).1
  have hAq : (c5GenericA r : ℚ) < (2 ^ 192 : ℚ) := by exact_mod_cast hA
  have hgrid : (2 ^ 192 : ℚ) < c5GenericGrid := by
    norm_num [c5GenericGrid]
  exact hAq.trans hgrid

lemma c5Generic_two_B_sq_lt_grid (r : ℕ) (hr : r ≤ 190) :
    2 * (c5GenericB r : ℚ) ^ 2 < c5GenericGrid := by
  have hB := (c5Generic_stage_parameters_bound r hr).2
  have hBq : (c5GenericB r : ℚ) < (2 ^ 192 : ℚ) := by exact_mod_cast hB
  have hB0 : 0 ≤ (c5GenericB r : ℚ) := Nat.cast_nonneg _
  have hpow : 0 ≤ (2 ^ 192 : ℚ) := by positivity
  have hsquare : (c5GenericB r : ℚ) ^ 2 ≤ (2 ^ 192 : ℚ) ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ (2 ^ 192 : ℚ) - c5GenericB r by linarith)
      (show 0 ≤ (2 ^ 192 : ℚ) + c5GenericB r by positivity)]
  calc
    2 * (c5GenericB r : ℚ) ^ 2 ≤ 2 * (2 ^ 192 : ℚ) ^ 2 := by nlinarith
    _ < c5GenericGrid := by norm_num [c5GenericGrid]

lemma c5GenericStageBox_zero :
    c5GenericStageBox 0 = c5ZeroExpStage2Export := by
  norm_num [c5GenericStageBox, c5GenericA, c5GenericB, c5GenericBox,
    c5GenericGrid, c5ZeroExpStage2Export, c5ZeroExpStage4Grid]

theorem c5GenericStageBox_coarsen (r : ℕ) (hr : r ≤ 190) :
    (c5GenericBoxSquare (c5GenericA r) (c5GenericB r)).coarsen 896 =
      c5GenericStageBox (r + 1) := by
  have hstep := c5GenericBox_square_coarsen (c5GenericA r) (c5GenericB r)
    (c5GenericA_lt_B r) (c5GenericA_lt_grid r hr)
    (c5Generic_two_B_sq_lt_grid r hr)
  simpa [c5GenericStageBox, ← c5GenericA_succ, ← c5GenericB_succ] using hstep

theorem c5RoundedExpC_zero_stage_generic :
    ∀ r ≤ 190,
      c5RoundedExpC 192 896 (r + 2) (ComplexInterval.exact 0 0) =
        c5GenericStageBox r := by
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
      intro hr
      cases r with
      | zero =>
          rw [c5ZeroExpStage2_eq, c5GenericStageBox_zero]
      | succ r =>
          have hr' : r ≤ 190 := by omega
          have hprev := ih r (by omega) hr'
          have hhalf : ComplexInterval.halveC (ComplexInterval.exact 0 0) =
              ComplexInterval.exact 0 0 := by
            simp [ComplexInterval.halveC, ComplexInterval.exact, Interval.exact,
              Interval.halve]
          have hnext := c5GenericStageBox_coarsen r hr'
          rw [show Nat.succ r + 2 = (r + 2) + 1 by omega]
          change ((c5RoundedExpC 192 896 (r + 2)
            (ComplexInterval.halveC (ComplexInterval.exact 0 0))).mul
              (c5RoundedExpC 192 896 (r + 2)
                (ComplexInterval.halveC (ComplexInterval.exact 0 0)))).coarsen 896 =
            c5GenericStageBox (r + 1)
          rw [hhalf, hprev]
          exact hnext

theorem c5RoundedExpC_zero_stage_2_to_192 (k : ℕ) (hk : 2 ≤ k) (hk' : k ≤ 192) :
    c5RoundedExpC 192 896 k (ComplexInterval.exact 0 0) =
      c5GenericStageBox (k - 2) := by
  have hr : k - 2 ≤ 190 := by omega
  have h := c5RoundedExpC_zero_stage_generic (k - 2) hr
  have hkEq : k - 2 + 2 = k := by omega
  simpa [hkEq] using h

theorem c5RoundedExpC_zero_stage_2_to_192_closed_form
    (k : ℕ) (hk : 2 ≤ k) (hk' : k ≤ 192) :
    c5RoundedExpC 192 896 k (ComplexInterval.exact 0 0) =
      c5GenericBox (3 * 2 ^ (k - 2) - 1) (4 * 2 ^ (k - 2) - 1) := by
  simpa [c5GenericStageBox, c5GenericA, c5GenericB] using
    c5RoundedExpC_zero_stage_2_to_192 k hk hk'
