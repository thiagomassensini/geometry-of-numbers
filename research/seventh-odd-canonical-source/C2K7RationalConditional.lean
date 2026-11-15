import K7PivotBridge
import OddTrialPositivity
import GeometryOfNumbers.Analysis.CarryMaterialSourceFactor

namespace CarrySeventhOddCanonical
open CarryIntegralCertificate CarrySelfAdjointOperator CarryCriticalSource
open GeometryOfNumbers.Analysis
open scoped BigOperators Matrix
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 48000000

/-! These are the exact outward-rounded rational boxes from the supplied
48-decimal certificate. They are hypotheses about the source until a C2
source-enclosure theorem proves membership; this module does not assert that
membership unconditionally. -/
def c2K7MomentBoxes : Fin 14 → Box := ![
  Box.finite 23104993115418970788933810430339014003381760397000000000000 23104993115418970788933810430339014003381760398000000000000,
  Box.finite 37172599285269686164866262471740578453650889000000000000 37172599285269686164866262471740578453650890000000000000,
  Box.finite 144173931400973279695381556094820907036883000000000000 144173931400973279695381556094820907036884000000000000,
  Box.finite 663031680252990869873272081961357248473000000000000 663031680252990869873272081961357248474000000000000,
  Box.finite 3213664150616601216102116599834655141000000000000 3213664150616601216102116599834655142000000000000,
  Box.finite 15876934514910153518982838808391042000000000000 15876934514910153518982838808391043000000000000,
  Box.finite 79033257240467379110989306173415000000000000 79033257240467379110989306173416000000000000,
  Box.finite 394647139999884613379632906639000000000000 394647139999884613379632906640000000000000,
  Box.finite 1973265073744967276523596221000000000000 1973265073744967276523596222000000000000,
  Box.finite 9872165383297157593570283000000000000 9872165383297157593570284000000000000,
  Box.finite 49402563522819790474708000000000000 49402563522819790474709000000000000,
  Box.finite 247249444432876934605000000000000 247249444432876934606000000000000,
  Box.finite 1237493444324996633000000000000 1237493444324996634000000000000,
  Box.finite 6193843423310201000000000000 6193843423310202000000000000]

def c2K7MomentBox (n : ℕ) : Box :=
  if hn : n < 14 then c2K7MomentBoxes ⟨n,hn⟩ else .all

theorem mem_c2K7MomentBox (hsource :
    ∀ q : Fin 14, (c2K7MomentBoxes q).Mem (h q.val)) (n : ℕ) :
    (c2K7MomentBox n).Mem (h n) := by
  by_cases hn : n < 14
  · simpa [c2K7MomentBox, hn] using hsource ⟨n,hn⟩
  · simp [c2K7MomentBox, hn, Box.Mem]

def c2K7ScaledPairing (i j : ℕ) : ℝ :=
  (200 : ℝ)^(i+j+1) * h (i+j+1)

def c2K7ScaledPairingBox (i j : ℕ) : Box :=
  (c2K7MomentBox (i+j+1)).mul (Box.point ((200 : ℤ)^(i+j+1)))

theorem mem_c2K7ScaledPairingBox (i j : ℕ)
    (hsource : ∀ r : Fin 14, (c2K7MomentBoxes r).Mem (h r.val)) :
    (c2K7ScaledPairingBox i j).Mem (c2K7ScaledPairing i j) := by
  have hm := mem_c2K7MomentBox hsource (i+j+1)
  have hp := mem_point ((200 : ℤ)^(i+j+1))
  have hx := mem_mul hm hp
  simpa [c2K7ScaledPairingBox, c2K7ScaledPairing, mul_comm] using hx

theorem c2K7ScaledPairing_symm (i j : ℕ) :
    c2K7ScaledPairing i j = c2K7ScaledPairing j i := by
  simp only [c2K7ScaledPairing]
  congr 2 <;> omega

def c2K7RemainderBox : ℕ → ℕ → ℕ → Box
  | 0, i, j => c2K7ScaledPairingBox i j
  | r+1, i, j => (c2K7RemainderBox r i j).add
      (((c2K7RemainderBox r i r).mul (c2K7RemainderBox r r j)).div
        (c2K7RemainderBox r r r)).neg

theorem mem_c2K7RemainderBox (r i j : ℕ) (hsource :
    ∀ q : Fin 14, (c2K7MomentBoxes q).Mem (h q.val)) :
    (c2K7RemainderBox r i j).Mem
      (carryPairingRemainder c2K7ScaledPairing r i j) := by
  induction r generalizing i j with
  | zero =>
      exact mem_c2K7ScaledPairingBox i j hsource
  | succ r ih =>
      simp only [c2K7RemainderBox, carryPairingRemainder]
      have hij := ih i j
      have hir := ih i r
      have hrj := ih r j
      have hrr := ih r r
      exact mem_add hij (mem_neg (mem_div (mem_mul hir hrj) hrr))

theorem c2K7_remainder_checks : ∀ r : Fin 7,
    (c2K7RemainderBox r.val r.val r.val).positive = true := by
  decide +kernel

theorem c2K7_scaled_pivots_pos (hsource :
    ∀ q : Fin 14, (c2K7MomentBoxes q).Mem (h q.val)) (r : ℕ) (hr : r < 7) :
    0 < carryPairingPivot c2K7ScaledPairing r := by
  have hm := mem_c2K7RemainderBox r r r hsource
  exact pos_of_mem hm (c2K7_remainder_checks ⟨r,hr⟩)

theorem c2K7_scaled_posDef (hsource :
    ∀ q : Fin 14, (c2K7MomentBoxes q).Mem (h q.val)) :
    Matrix.PosDef (fun i j : Fin 7 => c2K7ScaledPairing i.val j.val) :=
  carryPairingCholesky_posDef c2K7ScaledPairing_symm 7
    (c2K7_scaled_pivots_pos hsource)

private theorem c2K7_native_form_positive_of_boxes (hsource :
    ∀ q : Fin 14, (c2K7MomentBoxes q).Mem (h q.val)) (x : Fin 7 → ℝ) (hx : x ≠ 0) :
    0 < sourceMomentQuadratic h 1 7 x := by
  let y : Fin 7 → ℝ := fun i => x i / (200 : ℝ)^i.val
  have hy : y ≠ 0 := by
    intro he
    apply hx
    funext i
    have hi := congrFun he i
    dsimp [y] at hi
    exact (div_eq_zero_iff).mp hi |>.resolve_right (pow_ne_zero _ (by norm_num))
  have hp := (c2K7_scaled_posDef hsource).dotProduct_mulVec_pos hy
  have hform :
      y ⬝ᵥ ((fun i j : Fin 7 => c2K7ScaledPairing i.val j.val) *ᵥ y) =
        200 * sourceMomentQuadratic h 1 7 x := by
    simp only [Matrix.mulVec, dotProduct, sourceMomentQuadratic, sourceMomentMatrix,
      Pi.star_apply, star_trivial]
    calc
      _ = ∑ i : Fin 7, ∑ j : Fin 7,
          y i * c2K7ScaledPairing i.val j.val * y j := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            ring
      _ = ∑ i : Fin 7, ∑ j : Fin 7,
          (200 : ℝ) * (x i * h (i.val+j.val+1) * x j) := by
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro j hj
            dsimp [y, c2K7ScaledPairing]
            have hpow : (200 : ℝ)^(i.val+j.val+1) =
                200 * (200 : ℝ)^i.val * (200 : ℝ)^j.val := by
              rw [show i.val+j.val+1 = (i.val+j.val)+1 by omega, pow_succ,
                pow_add]
              ring
            rw [hpow]
            have hi0 : (200 : ℝ)^i.val ≠ 0 := pow_ne_zero _ (by norm_num)
            have hj0 : (200 : ℝ)^j.val ≠ 0 := pow_ne_zero _ (by norm_num)
            field_simp
      _ = 200 * (∑ i : Fin 7, x i * ∑ j : Fin 7,
          h (i.val+j.val+1) * x j) := by
            simp only [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro j hj
            ring
  change y ⬝ᵥ ((fun i j : Fin 7 => c2K7ScaledPairing i.val j.val) *ᵥ y) > 0 at hp
  rw [hform] at hp
  nlinarith

theorem c2K7_matrix_posDef_of_rational_source_boxes (hsource :
    ∀ q : Fin 14, (c2K7MomentBoxes q).Mem (h q.val)) :
    (sourceMomentMatrix h 1 7).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (sourceMomentMatrix_isHermitian h 1 7)
  intro x hx
  change 0 < sourceMomentQuadratic h 1 7 x
  exact c2K7_native_form_positive_of_boxes hsource x hx

theorem c2K7_pivot_pos_of_rational_source_boxes (hsource :
    ∀ q : Fin 14, (c2K7MomentBoxes q).Mem (h q.val)) :
    0 < sourceMomentSchur h 1 6 :=
  (k7_matrix_posDef_iff_pivot).mp
    (c2K7_matrix_posDef_of_rational_source_boxes hsource)

end
end CarrySeventhOddCanonical
