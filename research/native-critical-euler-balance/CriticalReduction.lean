import EulerPair

namespace CarryCriticalEuler
open CarrySelfAdjointOperator CarrySigmaSource CarryMovingSigma Matrix
open scoped BigOperators Matrix
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000

def eulerResidual (n : ℕ) (v : Fin (n+2) → ℝ) : Fin (n+1) → ℝ :=
  fun i => ((i.val:ℝ)-(n+1:ℕ))*v i.castSucc

def eulerSecondResidual (n : ℕ) (v : Fin (n+2) → ℝ) : Fin (n+1) → ℝ :=
  fun i => ((i.val:ℝ)^2-((n+1:ℕ):ℝ)^2)*v i.castSucc

theorem euler_residual_decomposition (n : ℕ) (v : Fin (n+2) → ℝ) :
    jetEuler v = ((n+1:ℕ):ℝ) • v + Fin.snoc (eulerResidual n v) 0 := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · simp [jetEuler]
  · intro j
    simp [jetEuler,eulerResidual]
    ring

theorem euler_second_residual_decomposition (n : ℕ) (v : Fin (n+2) → ℝ) :
    jetEuler (jetEuler v) = ((n+1:ℕ):ℝ)^2 • v + Fin.snoc (eulerSecondResidual n v) 0 := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · simp [jetEuler,pow_two]
    ring
  · intro j
    simp [jetEuler,eulerSecondResidual]
    ring

theorem pair_add_right (m : ℕ → ℝ) (s : ℕ) {N : ℕ} (x y z : Fin N → ℝ) :
    pair m s x (y+z) = pair m s x y + pair m s x z := by
  simp [pair,Matrix.mulVec_add,dotProduct_add]
theorem pair_add_left (m : ℕ → ℝ) (s : ℕ) {N : ℕ} (x y z : Fin N → ℝ) :
    pair m s (x+y) z = pair m s x z + pair m s y z := by
  simp [pair,add_dotProduct]
theorem pair_smul_right (m : ℕ → ℝ) (s : ℕ) {N : ℕ} (x y : Fin N → ℝ) (a : ℝ) :
    pair m s x (a • y) = a*pair m s x y := by
  simp [pair,Matrix.mulVec_smul,dotProduct_smul]
theorem pair_smul_left (m : ℕ → ℝ) (s : ℕ) {N : ℕ} (x y : Fin N → ℝ) (a : ℝ) :
    pair m s (a • x) y = a*pair m s x y := by
  simp [pair,smul_dotProduct]

theorem pair_snoc_zero_self (m : ℕ → ℝ) (s n : ℕ) (r : Fin (n+1) → ℝ) :
    pair m s (Fin.snoc r 0) (Fin.snoc r 0) = sourceMomentQuadratic m s (n+1) r := by
  simp [pair,sourceMomentQuadratic,Matrix.mulVec,dotProduct,Fin.sum_univ_castSucc,sourceMomentMatrix]

/-- Orthogonality eliminates the high mixed Euler terms exactly. The lower
residual is retained, in the original shifted moment form. -/
theorem stationary_weighted_reduction (m : ℕ → ℝ) (s n : ℕ) (v : Fin (n+2) → ℝ)
    (p : ℝ) (hrel : sourceMomentMatrix m s (n+2) *ᵥ v = Fin.snoc 0 p) :
    weightedForm m s v =
      ((2*((n+1:ℕ):ℝ)+(s:ℝ)+1)*(4*((n+1:ℕ):ℝ)+2*(s:ℝ)+3))*pair m (s+1) v v -
      (16*((n+1:ℕ):ℝ)+8*(s:ℝ)+6)*v (Fin.last n).castSucc*p +
      4*sourceMomentQuadratic m (s+1) (n+1) (eulerResidual n v) := by
  have hR := stationary_shift_pair m s n v p hrel (eulerResidual n v)
  have hT := stationary_shift_pair m s n v p hrel (eulerSecondResidual n v)
  have hr : pair m (s+1) v (Fin.snoc (eulerResidual n v) 0) =
      -v (Fin.last n).castSucc*p := by
    rw [hR]
    simp [eulerResidual]
    ring
  have ht : pair m (s+1) v (Fin.snoc (eulerSecondResidual n v) 0) =
      (1-2*((n+1:ℕ):ℝ))*v (Fin.last n).castSucc*p := by
    rw [hT]
    simp [eulerSecondResidual]
    ring
  rw [weighted_euler_identity]
  rw [euler_second_residual_decomposition n v,euler_residual_decomposition n v]
  simp only [pair_add_left,pair_add_right,pair_smul_left,pair_smul_right]
  rw [pair_symm m (s+1) (Fin.snoc (eulerResidual n v) 0) v,hr,ht,pair_snoc_zero_self]
  ring

/-- A sufficient bound after the old shifted residual is certified nonnegative.
The right side is a comparison of original scalar energies, not a sign axiom. -/
theorem stationary_weighted_lower (m : ℕ → ℝ) (s n : ℕ) (v : Fin (n+2) → ℝ)
    (p : ℝ) (hrel : sourceMomentMatrix m s (n+2) *ᵥ v = Fin.snoc 0 p)
    (hold : (sourceMomentMatrix m (s+1) (n+1)).PosSemidef) :
    ((2*((n+1:ℕ):ℝ)+(s:ℝ)+1)*(4*((n+1:ℕ):ℝ)+2*(s:ℝ)+3))*pair m (s+1) v v -
      (16*((n+1:ℕ):ℝ)+8*(s:ℝ)+6)*v (Fin.last n).castSucc*p ≤ weightedForm m s v := by
  rw [stationary_weighted_reduction m s n v p hrel]
  have h := hold.dotProduct_mulVec_nonneg (eulerResidual n v)
  change 0 ≤ sourceMomentQuadratic m (s+1) (n+1) (eulerResidual n v) at h
  linarith

end
end CarryCriticalEuler
