import HighSampleAmplitude17

namespace C3ShiftedFourth

open CarryC3Boxes

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 30000000

private def gridDenNat : ℕ := 10^30
private def gridDenInt : ℤ := 10^30
private def gridDenRat : ℚ := 10^30

/-- Integer interval endpoints measured in units of `10⁻³⁰`. -/
structure GridBox where
  lo : ℤ
  hi : ℤ
  deriving DecidableEq, Repr

def GridBox.toBox (a : GridBox) : Box :=
  ⟨(a.lo:ℚ) / gridDenRat, (a.hi:ℚ) / gridDenRat⟩

def GridBox.ofBox (a : Box) : GridBox :=
  ⟨⌊a.lo * gridDenRat⌋, ⌊a.hi * gridDenRat⌋ + 1⟩

def gpoint (z : ℤ) : GridBox := ⟨z * gridDenInt, z * gridDenInt⟩
def gzero : GridBox := ⟨0,0⟩
def gone : GridBox := gpoint 1

def gadd (a b : GridBox) : GridBox := ⟨a.lo+b.lo, a.hi+b.hi+1⟩
def gneg (a : GridBox) : GridBox := ⟨-a.hi,-a.lo⟩
def gsub (a b : GridBox) : GridBox := ⟨a.lo-b.hi,a.hi-b.lo+1⟩

def gmul (a b : GridBox) : GridBox :=
  ⟨min (min (a.lo*b.lo/gridDenInt) (a.lo*b.hi/gridDenInt))
      (min (a.hi*b.lo/gridDenInt) (a.hi*b.hi/gridDenInt)),
   max (max (a.lo*b.lo/gridDenInt) (a.lo*b.hi/gridDenInt))
      (max (a.hi*b.lo/gridDenInt) (a.hi*b.hi/gridDenInt)) + 1⟩

def gscale (a : GridBox) (q : ℚ) : GridBox :=
  ⟨⌊min ((a.lo:ℚ)*q) ((a.hi:ℚ)*q)⌋,
   ⌊max ((a.lo:ℚ)*q) ((a.hi:ℚ)*q)⌋+1⟩

def gpow (a : GridBox) : ℕ → GridBox
  | 0 => gone
  | n+1 => gmul (gpow a n) a

def gbsum (f : ℕ → GridBox) : ℕ → GridBox
  | 0 => gzero
  | n+1 => gadd (gbsum f n) (f n)

def gbsumFin {N : ℕ} (f : Fin N → GridBox) : GridBox :=
  gbsum (fun k => if hk : k < N then f ⟨k,hk⟩ else gzero) N

private theorem floor_min_rat (a b : ℚ) :
    ⌊min a b⌋ = min ⌊a⌋ ⌊b⌋ := by
  by_cases h : a ≤ b
  · rw [min_eq_left h, min_eq_left (Int.floor_mono h)]
  · have h' : b ≤ a := le_of_not_ge h
    rw [min_eq_right h', min_eq_right (Int.floor_mono h')]

private theorem floor_max_rat (a b : ℚ) :
    ⌊max a b⌋ = max ⌊a⌋ ⌊b⌋ := by
  by_cases h : a ≤ b
  · rw [max_eq_right h, max_eq_right (Int.floor_mono h)]
  · have h' : b ≤ a := le_of_not_ge h
    rw [max_eq_left h', max_eq_left (Int.floor_mono h')]

private theorem floor_min_mul_rat (a b c : ℚ) (hc : 0 ≤ c) :
    ⌊min a b * c⌋ = min ⌊a*c⌋ ⌊b*c⌋ := by
  by_cases h : a ≤ b
  · calc
      ⌊min a b * c⌋ = ⌊a*c⌋ := by rw [min_eq_left h]
      _ = min ⌊a*c⌋ ⌊b*c⌋ := (min_eq_left
        (Int.floor_mono (mul_le_mul_of_nonneg_right h hc))).symm
  · have h' : b ≤ a := le_of_not_ge h
    calc
      ⌊min a b * c⌋ = ⌊b*c⌋ := by rw [min_eq_right h']
      _ = min ⌊a*c⌋ ⌊b*c⌋ := (min_eq_right
        (Int.floor_mono (mul_le_mul_of_nonneg_right h' hc))).symm

private theorem floor_max_mul_rat (a b c : ℚ) (hc : 0 ≤ c) :
    ⌊max a b * c⌋ = max ⌊a*c⌋ ⌊b*c⌋ := by
  by_cases h : a ≤ b
  · calc
      ⌊max a b * c⌋ = ⌊b*c⌋ := by rw [max_eq_right h]
      _ = max ⌊a*c⌋ ⌊b*c⌋ := (max_eq_right
        (Int.floor_mono (mul_le_mul_of_nonneg_right h hc))).symm
  · have h' : b ≤ a := le_of_not_ge h
    calc
      ⌊max a b * c⌋ = ⌊a*c⌋ := by rw [max_eq_left h']
      _ = max ⌊a*c⌋ ⌊b*c⌋ := (max_eq_left
        (Int.floor_mono (mul_le_mul_of_nonneg_right h' hc))).symm

private theorem floor_int_product_div (x y : ℤ) :
    ⌊((x:ℚ)*(y:ℚ))/gridDenRat⌋ = x*y/gridDenInt := by
  have h : ((x:ℚ)*(y:ℚ))/gridDenRat = ((x*y:ℤ):ℚ)/(gridDenNat:ℚ) := by
    norm_num [gridDenRat, gridDenNat]
  rw [h, Rat.floor_intCast_div_natCast]
  norm_num [gridDenInt, gridDenNat]

private theorem grid_term_scale (x y : ℤ) :
    ((x:ℚ)/gridDenRat)*((y:ℚ)/gridDenRat)*gridDenRat =
      ((x*y:ℤ):ℚ)/gridDenRat := by
  have hs : gridDenRat ≠ 0 := by norm_num [gridDenRat]
  field_simp [hs]
  norm_cast

private theorem grid_scalar_scale (x : ℤ) (q : ℚ) :
    ((x:ℚ)/gridDenRat*q)*gridDenRat = (x:ℚ)*q := by
  have hs : gridDenRat ≠ 0 := by norm_num [gridDenRat]
  field_simp [hs]

private theorem floor_min4_grid (a b c d scale : ℚ)
    (hscale : 0 ≤ scale) :
    ⌊min (min a b) (min c d) * scale⌋ =
      min (min ⌊a*scale⌋ ⌊b*scale⌋) (min ⌊c*scale⌋ ⌊d*scale⌋) := by
  calc
    ⌊min (min a b) (min c d) * scale⌋ =
        min ⌊min a b * scale⌋ ⌊min c d * scale⌋ := by
          exact floor_min_mul_rat _ _ _ hscale
    _ = min (min ⌊a*scale⌋ ⌊b*scale⌋)
          (min ⌊c*scale⌋ ⌊d*scale⌋) := by
        rw [floor_min_mul_rat a b scale hscale,
          floor_min_mul_rat c d scale hscale]

private theorem floor_max4_grid (a b c d scale : ℚ)
    (hscale : 0 ≤ scale) :
    ⌊max (max a b) (max c d) * scale⌋ =
      max (max ⌊a*scale⌋ ⌊b*scale⌋) (max ⌊c*scale⌋ ⌊d*scale⌋) := by
  calc
    ⌊max (max a b) (max c d) * scale⌋ =
        max ⌊max a b * scale⌋ ⌊max c d * scale⌋ := by
          exact floor_max_mul_rat _ _ _ hscale
    _ = max (max ⌊a*scale⌋ ⌊b*scale⌋)
          (max ⌊c*scale⌋ ⌊d*scale⌋) := by
        rw [floor_max_mul_rat a b scale hscale,
          floor_max_mul_rat c d scale hscale]

private theorem roundLower_intGrid (z : ℤ) :
    roundLower ((z:ℚ)/gridDenRat) = (z:ℚ)/gridDenRat := by
  unfold roundLower gridScale
  have h : ((z:ℚ)/gridDenRat)*(10^30:ℚ) = (z:ℚ) := by
    norm_num [gridDenRat]
  rw [h]
  norm_num [gridDenRat]

private theorem roundUpper_intGrid (z : ℤ) :
    roundUpper ((z:ℚ)/gridDenRat) = ((z+1:ℤ):ℚ)/gridDenRat := by
  unfold roundUpper gridScale
  have h : ((z:ℚ)/gridDenRat)*(10^30:ℚ) = (z:ℚ) := by
    norm_num [gridDenRat]
  rw [h]
  norm_num [gridDenRat]

private theorem gridDen_cast : (gridDenInt:ℚ) = gridDenRat := by
  norm_num [gridDenInt, gridDenRat]

private theorem decodeIntGrid (z : ℤ) :
    ((z*gridDenInt:ℤ):ℚ)/gridDenRat = (z:ℚ) := by
  rw [Int.cast_mul, gridDen_cast]
  norm_num [gridDenInt, gridDenRat]

private theorem box_eq_of_endpoints {a b : Box}
    (hlo : a.lo = b.lo) (hhi : a.hi = b.hi) : a = b := by
  cases a with
  | mk alo ahi =>
    cases b with
    | mk blo bhi => simp_all

theorem grid_toBox_ofBox_contains (a : Box) :
    a.Subset (GridBox.toBox (GridBox.ofBox a)) := by
  have hs : (0:ℚ) < gridDenRat := by norm_num [gridDenRat]
  constructor
  · dsimp [GridBox.toBox, GridBox.ofBox]
    have h := Int.floor_le (a.lo * gridDenRat)
    calc
      (⌊a.lo * gridDenRat⌋:ℚ) / gridDenRat ≤ (a.lo * gridDenRat) / gridDenRat :=
        div_le_div_of_nonneg_right (by exact_mod_cast h) hs.le
      _ = a.lo := by field_simp [hs.ne']
  · dsimp [GridBox.toBox, GridBox.ofBox]
    have h := Int.lt_floor_add_one (a.hi * gridDenRat)
    have h' : a.hi * gridDenRat < (⌊a.hi * gridDenRat⌋ + 1 : ℤ) := by exact_mod_cast h
    exact (le_div_iff₀ hs).2 h'.le

theorem grid_toBox_gpoint (z : ℤ) : (gpoint z).toBox = Box.point z := by
  apply box_eq_of_endpoints <;> change ((z*gridDenInt:ℤ):ℚ)/gridDenRat = (z:ℚ)
  all_goals exact decodeIntGrid z

theorem grid_toBox_gadd (a b : GridBox) :
    (gadd a b).toBox = badd a.toBox b.toBox := by
  apply box_eq_of_endpoints
  · change ((a.lo+b.lo:ℤ):ℚ)/gridDenRat =
      roundLower ((a.lo:ℚ)/gridDenRat+(b.lo:ℚ)/gridDenRat)
    rw [show (a.lo:ℚ)/gridDenRat+(b.lo:ℚ)/gridDenRat =
      ((a.lo+b.lo:ℤ):ℚ)/gridDenRat by push_cast; ring]
    exact (roundLower_intGrid _).symm
  · change ((a.hi+b.hi+1:ℤ):ℚ)/gridDenRat =
      roundUpper ((a.hi:ℚ)/gridDenRat+(b.hi:ℚ)/gridDenRat)
    rw [show (a.hi:ℚ)/gridDenRat+(b.hi:ℚ)/gridDenRat =
      ((a.hi+b.hi:ℤ):ℚ)/gridDenRat by push_cast; ring]
    exact (roundUpper_intGrid _).symm

theorem grid_toBox_gneg (a : GridBox) :
    (gneg a).toBox = bneg a.toBox := by
  apply box_eq_of_endpoints <;> simp [GridBox.toBox, gneg, bneg, Box.neg,
    neg_div]

theorem grid_toBox_gsub (a b : GridBox) :
    (gsub a b).toBox = bsub a.toBox b.toBox := by
  apply box_eq_of_endpoints
  · dsimp only [GridBox.toBox, gsub, bsub, Box.round, Box.sub, Box.add, Box.neg]
    rw [show (a.lo:ℚ)/gridDenRat+ -((b.hi:ℚ)/gridDenRat) =
      ((a.lo-b.hi:ℤ):ℚ)/gridDenRat by push_cast; ring]
    exact (roundLower_intGrid _).symm
  · dsimp only [GridBox.toBox, gsub, bsub, Box.round, Box.sub, Box.add, Box.neg]
    rw [show (a.hi:ℚ)/gridDenRat+ -((b.lo:ℚ)/gridDenRat) =
      ((a.hi-b.lo:ℤ):ℚ)/gridDenRat by push_cast; ring]
    exact (roundUpper_intGrid _).symm

theorem grid_toBox_gmul (a b : GridBox) :
    (gmul a b).toBox = bmul a.toBox b.toBox := by
  apply box_eq_of_endpoints
  · dsimp only [GridBox.toBox, gmul, bmul, Box.round, Box.mul]
    simp only [Int.cast_min]
    unfold roundLower
    rw [show gridScale = gridDenRat by norm_num [gridScale, gridDenRat]]
    rw [floor_min4_grid _ _ _ _ gridDenRat (by norm_num [gridDenRat])]
    simp_rw [grid_term_scale]
    simp only [Int.cast_mul, floor_int_product_div]
    simp only [Int.cast_min]
  · dsimp only [GridBox.toBox, gmul, bmul, Box.round, Box.mul]
    unfold roundUpper
    rw [show gridScale = gridDenRat by norm_num [gridScale, gridDenRat]]
    rw [floor_max4_grid _ _ _ _ gridDenRat (by norm_num [gridDenRat])]
    simp_rw [grid_term_scale]
    simp only [Int.cast_mul, floor_int_product_div]

theorem grid_toBox_gscale (a : GridBox) (q : ℚ) :
    (gscale a q).toBox = bmul a.toBox (Box.point q) := by
  apply box_eq_of_endpoints
  · dsimp only [GridBox.toBox, gscale, bmul, Box.round, Box.mul, Box.point]
    unfold roundLower
    rw [show gridScale = gridDenRat by norm_num [gridScale, gridDenRat]]
    simp_rw [floor_min_mul_rat _ _ gridDenRat (by norm_num [gridDenRat])]
    simp_rw [grid_scalar_scale]
    simp only [min_self]
    rw [floor_min_rat]
  · dsimp only [GridBox.toBox, gscale, bmul, Box.round, Box.mul, Box.point]
    unfold roundUpper
    rw [show gridScale = gridDenRat by norm_num [gridScale, gridDenRat]]
    simp_rw [floor_max_mul_rat _ _ gridDenRat (by norm_num [gridDenRat])]
    simp_rw [grid_scalar_scale]
    simp only [max_self]
    rw [floor_max_rat]

theorem grid_toBox_gpow (a : GridBox) (n : ℕ) :
    (gpow a n).toBox = bpow a.toBox n := by
  induction n with
  | zero => simpa [gpow, bpow, gone] using grid_toBox_gpoint 1
  | succ n ih => rw [gpow, bpow, grid_toBox_gmul, ih]

theorem grid_toBox_gbsum (f : ℕ → GridBox) (n : ℕ) :
    (gbsum f n).toBox = CarryC3Boxes.bsum (fun k => (f k).toBox) n := by
  induction n with
  | zero => simp [gbsum, CarryC3Boxes.bsum, GridBox.toBox, gzero, Box.point]
  | succ n ih => rw [gbsum, CarryC3Boxes.bsum, grid_toBox_gadd, ih]

theorem grid_toBox_gbsumFin {N : ℕ} (f : Fin N → GridBox) :
    (gbsumFin f).toBox = CarryC3Boxes.bsumFin (fun i => (f i).toBox) := by
  rw [gbsumFin, CarryC3Boxes.bsumFin, grid_toBox_gbsum]
  congr 1
  funext k
  by_cases hk : k < N
  · simp [hk]
  · simp [hk, gzero, GridBox.toBox, Box.point, gridDenRat]

end
end C3ShiftedFourth
