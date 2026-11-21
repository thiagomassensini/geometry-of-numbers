import SigmaTwoPoleModel
import NativeTwoModeSlopeSignAdversary

/-!
# EXPLICIT ADVERSSARIAL PENCIL: SAME EXACT TWO REAL NODES, OPPOSITE PSD

Uses the pre-existing SigmaTwoPoleModel's unrestricted pencil factorization
for +1 and -1 real residues at EXACTLY the SAME two positive real nodes:
ρ1=1/2, ρ2=1/4. The pencil sees the same two roots even when the
second moment weight changes sign. The 2x2 Hankel determinant reverses.

This is a synthetic model, NOT an identification with native C2/F(z),
and does not assume RH, the spectral zeros, or analytic continuation.
-/

namespace CarryWheelNativeSignedGate
open CarrySigmaPade
open scoped Matrix

noncomputable section

private def toyPencil (w : ℝ) (s : ℕ) (lam : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (twoRealPoleShifted 1 w (1/2) (1/4) s).map (algebraMap ℝ ℂ) -
    lam • (twoRealPoleGram 1 w (1/2) (1/4) s).map (algebraMap ℝ ℂ)

/-- The pencil has BOTH exact inverse-square modes 1/2 and 1/4 as
generalized eigenvalues, REGARDLESS of the second signed residue. -/
theorem toySignedPencil_has_first_mode (w : ℝ) (s : ℕ) :
    (toyPencil w s (1/2 : ℂ)).det = 0 := by
  have h := twoRealPolePencil_characteristic
    1 w (1/2) (1/4) s (1/2 : ℂ)
  simpa [toyPencil] using h

theorem toySignedPencil_has_second_mode (w : ℝ) (s : ℕ) :
    (toyPencil w s (1/4 : ℂ)).det = 0 := by
  have h := twoRealPolePencil_characteristic
    1 w (1/2) (1/4) s (1/4 : ℂ)
  simpa [toyPencil] using h

theorem toySamePencilModes_but_opposite_Gram_signs (s : ℕ) :
    (0 < (twoRealPoleGram 1 1 (1/2) (1/4) s).det) ∧
    ((twoRealPoleGram 1 (-1) (1/2) (1/4) s).det < 0) ∧
    (toyPencil 1 s (1/2 : ℂ)).det = 0 ∧
    (toyPencil 1 s (1/4 : ℂ)).det = 0 ∧
    (toyPencil (-1) s (1/2 : ℂ)).det = 0 ∧
    (toyPencil (-1) s (1/4 : ℂ)).det = 0 := by
  constructor
  · rw [twoRealPoleGram_det]
    positivity
  constructor
  · rw [twoRealPoleGram_det]
    norm_num
  exact ⟨toySignedPencil_has_first_mode 1 s,
    toySignedPencil_has_second_mode 1 s,
    toySignedPencil_has_first_mode (-1) s,
    toySignedPencil_has_second_mode (-1) s⟩

end
end CarryWheelNativeSignedGate
