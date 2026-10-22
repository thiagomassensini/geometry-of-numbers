import GreenTailBounds

/-! Exact discrete tail acceleration on the original address lattice. This
is a finite identity, not an asserted infinite error estimate. The next
analytic obligation is to bound its fourth-difference remainder. -/
namespace CarryCellTail
open GeometryOfNumbers.Analysis GeometryOfNumbers.Analysis.BaseTwoCompletion
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000

def delta2 (f : ℕ → ℂ) (a : ℕ) : ℂ := f (a+2)-2*f (a+1)+f a
def delta4 (f : ℕ → ℂ) (a : ℕ) : ℂ :=
  f (a+4)-4*f (a+3)+6*f (a+2)-4*f (a+1)+f a

def tailBoundary (f : ℕ → ℂ) (a : ℕ) : ℂ := (3*f (a+2)-8*f (a+1)+5*f a)/8
def tailRemainder (f : ℕ → ℂ) (a : ℕ) : ℂ :=
  (3/8:ℂ)*delta4 f a+(1/2:ℂ)*delta4 f (a+1)+(3/8:ℂ)*delta4 f (a+2)

theorem tail_acceleration_cell (f : ℕ → ℂ) (a : ℕ) :
    delta2 f a = tailBoundary f a-tailBoundary f (a+4)+tailRemainder f a := by
  simp only [delta2, tailBoundary, tailRemainder, delta4, Nat.add_assoc]
  norm_num
  ring

/-- No asymptotic exchange: both endpoint terms and every remainder cell
are retained at a finite cutoff. -/
theorem tail_acceleration_finite (f : ℕ → ℂ) (a N : ℕ) :
    (∑ k ∈ Finset.range N, delta2 f (a+4*k)) =
      tailBoundary f a-tailBoundary f (a+4*N)+
        ∑ k ∈ Finset.range N, tailRemainder f (a+4*k) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ, tail_acceleration_cell]
    rw [show a+4*(N+1) = a+4*N+4 by omega]
    ring

theorem native_cell_delta2 (t : ℝ) (k : ℕ) :
    baseTwoCriticalCenterCell t k = delta2 (criticalMaterialSample t) (4*k+3) := by
  unfold baseTwoCriticalCenterCell delta2
  have hl : baseTwoLeftLeg k = 4*k+3 := by simp only [baseTwo_leftLeg_eq]; omega
  have hc : baseTwoCenter k = 4*k+3+1 := by simp only [baseTwo_center_eq]; omega
  have hr : baseTwoRightLeg k = 4*k+3+2 := by simp only [baseTwo_rightLeg_eq]; omega
  rw [hl, hc, hr]
  ring

/-- Exact whole-cell tail window of the SAME native source, including its
phase and two legs. It does not modify the source, camera or completion. -/
theorem native_tail_window_acceleration (t : ℝ) (M N : ℕ) :
    (∑ k ∈ Finset.range N, baseTwoCriticalCenterCell t (k+M)) =
      tailBoundary (criticalMaterialSample t) (4*M+3)-
        tailBoundary (criticalMaterialSample t) (4*M+3+4*N)+
      ∑ k ∈ Finset.range N, tailRemainder (criticalMaterialSample t) (4*M+3+4*k) := by
  simp_rw [native_cell_delta2, show ∀ k : ℕ, 4*(k+M)+3 = 4*M+3+4*k by omega]
  exact tail_acceleration_finite _ _ _
end
end CarryCellTail
