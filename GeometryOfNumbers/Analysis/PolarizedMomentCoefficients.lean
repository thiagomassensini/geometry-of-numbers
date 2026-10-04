import GeometryOfNumbers.Analysis.ParityMomentGram

/-!
# Real polarized moment coefficients

This is coefficient algebra only. It neither constructs vectors from moments
nor identifies any physical TFVD readout with these coefficients.
-/
namespace GeometryOfNumbers.Analysis

/-- Taylor order associated with each parity label; not a material address or depth. -/
def parityJetNumber : (ℕ ⊕ ℕ) → ℕ
  | Sum.inl n => 2 * n
  | Sum.inr n => 2 * n + 1

/-- The real diagonal coefficient, with zero odd entries. -/
def realMomentDiagonalCoefficient (moments : ℕ → ℝ) (n : ℕ) : ℝ :=
  if Even n then moments (n / 2) else 0

/-- Polarization depends on the combined order, independently of any carrier. -/
def polarizedRealMomentCoefficient (moments : ℕ → ℝ) (p q : ℕ) : ℝ :=
  realMomentDiagonalCoefficient moments (p + q)

theorem parityJetNumber_injective : Function.Injective parityJetNumber := by
  intro i j h
  cases i <;> cases j <;> simp only [parityJetNumber] at h
  · congr 1; omega
  · omega
  · omega
  · congr 1; omega

theorem realMomentDiagonalCoefficient_even (moments : ℕ → ℝ) (n : ℕ) :
    realMomentDiagonalCoefficient moments (2 * n) = moments n := by
  have he : Even (2 * n) := ⟨n, by omega⟩
  simp [realMomentDiagonalCoefficient, he]

theorem realMomentDiagonalCoefficient_odd (moments : ℕ → ℝ) (n : ℕ) :
    realMomentDiagonalCoefficient moments (2 * n + 1) = 0 := by
  have he : ¬ Even (2 * n + 1) := by
    rintro ⟨k, hk⟩
    omega
  simp [realMomentDiagonalCoefficient, he]

theorem polarizedRealMomentCoefficient_even_even (moments : ℕ → ℝ) (i j : ℕ) :
    polarizedRealMomentCoefficient moments (2 * i) (2 * j) = moments (i + j) := by
  unfold polarizedRealMomentCoefficient
  rw [show 2 * i + 2 * j = 2 * (i + j) by omega]
  exact realMomentDiagonalCoefficient_even moments (i + j)

theorem polarizedRealMomentCoefficient_odd_odd (moments : ℕ → ℝ) (i j : ℕ) :
    polarizedRealMomentCoefficient moments (2 * i + 1) (2 * j + 1) =
      moments (i + j + 1) := by
  unfold polarizedRealMomentCoefficient
  rw [show 2 * i + 1 + (2 * j + 1) = 2 * (i + j + 1) by omega]
  exact realMomentDiagonalCoefficient_even moments (i + j + 1)

theorem polarizedRealMomentCoefficient_even_odd (moments : ℕ → ℝ) (i j : ℕ) :
    polarizedRealMomentCoefficient moments (2 * i) (2 * j + 1) = 0 := by
  unfold polarizedRealMomentCoefficient
  rw [show 2 * i + (2 * j + 1) = 2 * (i + j) + 1 by omega]
  exact realMomentDiagonalCoefficient_odd moments (i + j)

theorem polarizedRealMomentCoefficient_odd_even (moments : ℕ → ℝ) (i j : ℕ) :
    polarizedRealMomentCoefficient moments (2 * i + 1) (2 * j) = 0 := by
  unfold polarizedRealMomentCoefficient
  rw [show 2 * i + 1 + 2 * j = 2 * (i + j) + 1 by omega]
  exact realMomentDiagonalCoefficient_odd moments (i + j)

/-- Exact compatibility with the already formalized parity Gram API. -/
theorem polarizedRealMomentCoefficient_eq_parityMomentKernel
    (moments : ℕ → ℝ) (i j : ℕ ⊕ ℕ) :
    polarizedRealMomentCoefficient moments (parityJetNumber i) (parityJetNumber j) =
      parityMomentKernel moments i j := by
  cases i <;> cases j <;> simp only [parityJetNumber, parityMomentKernel]
  · exact polarizedRealMomentCoefficient_even_even _ _ _
  · exact polarizedRealMomentCoefficient_even_odd _ _ _
  · exact polarizedRealMomentCoefficient_odd_even _ _ _
  · exact polarizedRealMomentCoefficient_odd_odd _ _ _

/-- Moving one order from the right to the left preserves the coefficient. -/
theorem polarizedRealMomentCoefficient_shift (moments : ℕ → ℝ) (p q : ℕ) :
    polarizedRealMomentCoefficient moments p (q + 1) =
      polarizedRealMomentCoefficient moments (p + 1) q := by
  unfold polarizedRealMomentCoefficient
  congr 1
  omega

end GeometryOfNumbers.Analysis
