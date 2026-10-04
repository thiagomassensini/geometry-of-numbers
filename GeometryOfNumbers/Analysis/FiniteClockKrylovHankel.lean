import GeometryOfNumbers.Analysis.SymmetricKrylovHankel
import GeometryOfNumbers.Analysis.FiniteMaterialClockJets

/-!
# Exact finite material-clock Krylov and temporal-jet crosswalk

L is the existing symmetric material log clock. The strong orbital generator
is -i L, not a self-adjoint clock. Spectral moments below are auxiliary moments
of a given finite vector, not the canonical dressed log-derivative sequence.
-/
namespace GeometryOfNumbers.Analysis.FiniteClockKrylov
noncomputable section
open NativeMaterialClock FiniteClockJets
open scoped ComplexConjugate

private theorem real_inner_re {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [InnerProductSpace ℝ H] (x y : H) :
    inner ℝ x y = (inner ℂ x y).re := by
  rw [real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two]
  exact (re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two
    (𝕜 := ℂ) x y).symm

/-- Powers of the already-defined material clock, with coordinate n=j+1. -/
theorem finiteMaterialClock_pow_apply {M : ℕ} (r : ℕ)
    (v : FiniteRealSpectralHilbert M) (j : Fin M) :
    (finiteMaterialClock M ^ r) v j = (finiteRealSpectralFrequency j : ℂ) ^ r * v j := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ']
    change (finiteRealSpectralFrequency j : ℂ) * ((finiteMaterialClock M ^ r) v j) = _
    rw [ih, pow_succ']
    ring

/-- The phase powers are explicit; the strong generator is not renamed L. -/
theorem finiteClockStrongGenerator_pow_eq_clockPow {M : ℕ} (r : ℕ)
    (v : FiniteRealSpectralHilbert M) :
    (finiteClockStrongGenerator M ^ r) v =
      (-Complex.I) ^ r • (finiteMaterialClock M ^ r) v := by
  ext j
  simp only [finiteClockStrongGenerator_pow_apply, finiteMaterialClock_pow_apply,
    PiLp.smul_apply, smul_eq_mul, clockRate, mul_pow, mul_assoc]

/-- Raw temporal derivative = (-i)^r times the symmetric Krylov vector. -/
theorem finiteMaterialClockJet_eq_krylov {M : ℕ} (r : ℕ)
    (v : FiniteRealSpectralHilbert M) :
    iteratedDeriv r (fun t : ℝ => finiteMaterialOrbit M t v) 0 =
      (-Complex.I) ^ r • (finiteMaterialClock M ^ r) v := by
  rw [finiteMaterialClockJet_eq_generatorPow, finiteClockStrongGenerator_pow_eq_clockPow]

/-- Normalized Taylor coefficient retains BOTH phase and factorial. -/
theorem normalizedClockJet_eq_krylov {M : ℕ} (r : ℕ)
    (v : FiniteRealSpectralHilbert M) :
    normalizedClockJet r v = ((r.factorial : ℂ)⁻¹ * (-Complex.I) ^ r) •
      (finiteMaterialClock M ^ r) v := by
  rw [normalizedClockJet, finiteClockStrongGenerator_pow_eq_clockPow, smul_smul]

/-- No information is lost: dephase and denormalize the existing jet. -/
theorem finiteClockKrylov_eq_dephasedClockJet {M : ℕ} (r : ℕ)
    (v : FiniteRealSpectralHilbert M) :
    (finiteMaterialClock M ^ r) v =
      ((r.factorial : ℂ) * Complex.I ^ r) • normalizedClockJet r v := by
  rw [normalizedClockJet_eq_krylov, smul_smul]
  have hf : (r.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
  have hi : Complex.I ^ r * (-Complex.I) ^ r = 1 := by
    rw [← mul_pow]
    norm_num [← neg_mul]
  have hc : ((r.factorial : ℂ) * Complex.I ^ r) *
      ((r.factorial : ℂ)⁻¹ * (-Complex.I) ^ r) = 1 := by
    calc
      _ = ((r.factorial : ℂ) * (r.factorial : ℂ)⁻¹) *
        (Complex.I ^ r * (-Complex.I) ^ r) := by ring
      _ = 1 := by rw [mul_inv_cancel₀ hf, hi, mul_one]
  rw [hc, one_smul]

/-- Skew symmetry of -i L makes the distinction between the two operators literal. -/
theorem finiteClockStrongGenerator_skew_inner {M : ℕ}
    (x y : FiniteRealSpectralHilbert M) :
    inner ℂ (finiteClockStrongGenerator M x) y =
      -inner ℂ x (finiteClockStrongGenerator M y) := by
  change inner ℂ ((-Complex.I) • finiteMaterialClock M x) y =
    -inner ℂ x ((-Complex.I) • finiteMaterialClock M y)
  rw [inner_smul_left, inner_smul_right, finiteRealSpectralGenerator_isSymmetric M x y]
  simp

/-- This sequence is defined from a given vector; it is not the canonical h. -/
def finiteClockSpectralMoment {M : ℕ} (v : FiniteRealSpectralHilbert M) (r : ℕ) : ℝ :=
  (inner ℂ v ((finiteMaterialClock M ^ r) v)).re

/-- The finite clock's own moments form a Hankel Gram on its real carrier. -/
theorem finiteClockSpectralMoment_gramRepresentation {M : ℕ}
    (v : FiniteRealSpectralHilbert M) :
    IsMomentGramRepresentation (finiteClockSpectralMoment v)
      (fun r => (finiteMaterialClock M ^ r) v) := by
  intro i j
  change (inner ℂ v ((finiteMaterialClock M ^ (i+j)) v)).re =
    inner ℝ ((finiteMaterialClock M ^ i) v) ((finiteMaterialClock M ^ j) v)
  rw [real_inner_re, symmetricKrylov_inner_add _ (finiteRealSpectralGenerator_isSymmetric M)]

/-- Exact complex jet Gram: conjugate the LEFT phase, retain both factorials. -/
theorem normalizedClockJet_inner_eq_krylov {M : ℕ}
    (v : FiniteRealSpectralHilbert M) (i j : ℕ) :
    inner ℂ (normalizedClockJet i v) (normalizedClockJet j v) =
      conj ((i.factorial : ℂ)⁻¹ * (-Complex.I) ^ i) *
        ((j.factorial : ℂ)⁻¹ * (-Complex.I) ^ j) *
          inner ℂ v ((finiteMaterialClock M ^ (i+j)) v) := by
  rw [normalizedClockJet_eq_krylov, normalizedClockJet_eq_krylov,
    inner_smul_left, inner_smul_right,
    symmetricKrylov_inner_add _ (finiteRealSpectralGenerator_isSymmetric M)]
  ring

/-- Existing head readout, with its exact phase/factorial multiplier. This is
still the finite HEAD, not the completed/dressed canonical moment sequence. -/
theorem finiteClockHeadCoefficient_eq_krylovReadout {M : ℕ}
    (weights : Fin M → ℝ) (r : ℕ) :
    historicalFiniteHeadCoefficient weights r =
      ((r.factorial : ℂ)⁻¹ * (-Complex.I) ^ r) *
        finiteHeadReadout weights ((finiteMaterialClock M ^ r) (historicalInitialState M)) := by
  rw [finiteClockJets_to_head, normalizedClockJet_eq_krylov, map_smul]
  rfl


/-- Power pairings are real because every power of the symmetric clock is symmetric. -/
theorem finiteClockKrylov_inner_complex {M : ℕ}
    (v : FiniteRealSpectralHilbert M) (i j : ℕ) :
    inner ℂ ((finiteMaterialClock M ^ i) v) ((finiteMaterialClock M ^ j) v) =
      (finiteClockSpectralMoment v (i+j) : ℂ) := by
  rw [symmetricKrylov_inner_add _ (finiteRealSpectralGenerator_isSymmetric M)]
  exact (((finiteRealSpectralGenerator_isSymmetric M).pow (i+j)).coe_re_inner_self_apply v).symm


/-- The original even normalized jet first column has an alternating sign and
an even factorial; it is not silently renamed a spectral moment. -/
theorem finiteClockEvenJet_firstColumn {M : ℕ}
    (v : FiniteRealSpectralHilbert M) (r : ℕ) :
    inner ℝ (normalizedClockJet (2*r) v) v =
      ((-1 : ℝ) ^ r / ((2*r).factorial : ℝ)) * finiteClockSpectralMoment v (2*r) := by
  rw [real_inner_re, normalizedClockJet_eq_krylov, inner_smul_left]
  have hi : inner ℂ ((finiteMaterialClock M ^ (2*r)) v) v =
      (finiteClockSpectralMoment v (2*r) : ℂ) := by
    simpa using finiteClockKrylov_inner_complex v (2*r) 0
  rw [hi]
  have hp : (-Complex.I) ^ (2*r) = (-1 : ℂ) ^ r := by
    rw [pow_mul]
    norm_num
  rw [hp]
  have hc : ((2*r).factorial : ℂ)⁻¹ * (-1 : ℂ) ^ r =
      (((((2*r).factorial : ℝ)⁻¹ * (-1 : ℝ) ^ r) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hc, Complex.conj_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [div_eq_mul_inv]
  ring

/-- The real first column of the original odd normalized jets vanishes; the
odd vectors themselves need not vanish. -/
theorem finiteClockOddJet_firstColumn {M : ℕ}
    (v : FiniteRealSpectralHilbert M) (r : ℕ) :
    inner ℝ (normalizedClockJet (2*r+1) v) v = 0 := by
  rw [real_inner_re, normalizedClockJet_eq_krylov, inner_smul_left]
  have hi : inner ℂ ((finiteMaterialClock M ^ (2*r+1)) v) v =
      (finiteClockSpectralMoment v (2*r+1) : ℂ) := by
    simpa using finiteClockKrylov_inner_complex v (2*r+1) 0
  rw [hi]
  have hp : (-Complex.I) ^ (2*r+1) = (-1 : ℂ) ^ r * (-Complex.I) := by
    rw [pow_succ, pow_mul]
    norm_num
  rw [hp]
  have hc : ((2*r+1).factorial : ℂ)⁻¹ * ((-1 : ℂ) ^ r * (-Complex.I)) =
      (((((2*r+1).factorial : ℝ)⁻¹ * (-1 : ℝ) ^ r) : ℝ) : ℂ) * (-Complex.I) := by
    push_cast
    ring
  rw [hc]
  simp only [map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I, neg_neg,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]

/-- No automatic raw-power even/odd orthogonality, already at material n=2. -/
theorem finiteClockRawKrylov_even_odd_pairing :
    inner ℝ (finiteMaterialBasis (1 : Fin 2))
      (finiteMaterialClock 2 (finiteMaterialBasis (1 : Fin 2))) = Real.log 2 := by
  rw [real_inner_re, finiteMaterialClock_basis]
  simp [inner_smul_right, finiteMaterialBasis, Complex.log_re]

theorem finiteClockRawKrylov_even_odd_pairing_pos :
    0 < inner ℝ (finiteMaterialBasis (1 : Fin 2))
      (finiteMaterialClock 2 (finiteMaterialBasis (1 : Fin 2))) := by
  rw [finiteClockRawKrylov_even_odd_pairing]
  exact Real.log_pos (by norm_num)

/-- Two REAL quadratures of the same clock orbit, before mentioning moments.
Odd vectors retain -i from the temporal generator; no mixed pairing is assumed. -/
def finiteClockParityKrylov {M : ℕ} (v : FiniteRealSpectralHilbert M) :
    (ℕ ⊕ ℕ) → FiniteRealSpectralHilbert M
  | Sum.inl r => (finiteMaterialClock M ^ (2*r)) v
  | Sum.inr r => (-Complex.I) • (finiteMaterialClock M ^ (2*r+1)) v


/-- Parity quadratures are derived from the original normalized temporal jets,
with the exact even factorial and alternating sign. -/
theorem finiteClockParityKrylov_even_eq_normalizedJet {M : ℕ}
    (v : FiniteRealSpectralHilbert M) (r : ℕ) :
    finiteClockParityKrylov v (Sum.inl r) =
      ((-1 : ℂ) ^ r * ((2*r).factorial : ℂ)) • normalizedClockJet (2*r) v := by
  rw [normalizedClockJet_eq_krylov, smul_smul]
  have hf : ((2*r).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (2*r)
  have hp : (-Complex.I) ^ (2*r) = (-1 : ℂ) ^ r := by
    rw [pow_mul]
    norm_num
  have hs : (-1 : ℂ) ^ r * (-1 : ℂ) ^ r = 1 := by
    rw [← mul_pow]
    norm_num
  have hc : ((-1 : ℂ) ^ r * ((2*r).factorial : ℂ)) *
      (((2*r).factorial : ℂ)⁻¹ * (-Complex.I) ^ (2*r)) = 1 := by
    rw [hp]
    calc
      _ = (((2*r).factorial : ℂ) * ((2*r).factorial : ℂ)⁻¹) *
          ((-1 : ℂ) ^ r * (-1 : ℂ) ^ r) := by ring
      _ = 1 := by rw [mul_inv_cancel₀ hf, hs, mul_one]
  rw [hc, one_smul]
  rfl

/-- Odd factorial and alternating sign preserve the generator's -i quadrature. -/
theorem finiteClockParityKrylov_odd_eq_normalizedJet {M : ℕ}
    (v : FiniteRealSpectralHilbert M) (r : ℕ) :
    finiteClockParityKrylov v (Sum.inr r) =
      ((-1 : ℂ) ^ r * ((2*r+1).factorial : ℂ)) • normalizedClockJet (2*r+1) v := by
  rw [normalizedClockJet_eq_krylov, smul_smul]
  have hf : ((2*r+1).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (2*r+1)
  have hp : (-Complex.I) ^ (2*r+1) = (-1 : ℂ) ^ r * (-Complex.I) := by
    rw [pow_succ, pow_mul]
    norm_num
  have hs : (-1 : ℂ) ^ r * (-1 : ℂ) ^ r = 1 := by
    rw [← mul_pow]
    norm_num
  have hc : ((-1 : ℂ) ^ r * ((2*r+1).factorial : ℂ)) *
      (((2*r+1).factorial : ℂ)⁻¹ * (-Complex.I) ^ (2*r+1)) = -Complex.I := by
    rw [hp]
    calc
      _ = (((2*r+1).factorial : ℂ) * ((2*r+1).factorial : ℂ)⁻¹) *
          ((-1 : ℂ) ^ r * (-1 : ℂ) ^ r) * (-Complex.I) := by ring
      _ = -Complex.I := by rw [mul_inv_cancel₀ hf, hs, mul_one, one_mul]
  rw [hc]
  rfl

/-- This REAL parity Gram realizes the even-power spectral sequence of L
(equivalently moments of L²), not an asserted canonical moment sequence. -/
theorem finiteClockParityKrylov_gramRepresentation {M : ℕ}
    (v : FiniteRealSpectralHilbert M) :
    IsParityMomentGramRepresentation (fun r => finiteClockSpectralMoment v (2*r))
      (finiteClockParityKrylov v) := by
  intro i j
  cases i <;> cases j <;>
    simp [parityMomentKernel, Matrix.gram, finiteClockParityKrylov,
      real_inner_re, inner_smul_left, inner_smul_right, finiteClockKrylov_inner_complex,
      Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  congr 1
  omega

/-- Consequence for these auxiliary spectral moments, with no positivity input. -/
theorem finiteClockEvenSpectralMoment_hankelPair_posSemidef {M : ℕ}
    (v : FiniteRealSpectralHilbert M) (N : ℕ) :
    (hankelGram (fun r => finiteClockSpectralMoment v (2*r)) N).PosSemidef ∧
      (shiftedHankel (fun r => finiteClockSpectralMoment v (2*r)) N).PosSemidef :=
  hankelPair_posSemidef_of_parityMomentGram (finiteClockParityKrylov_gramRepresentation v) N

end
end GeometryOfNumbers.Analysis.FiniteClockKrylov
