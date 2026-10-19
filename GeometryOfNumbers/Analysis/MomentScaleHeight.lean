import GeometryOfNumbers.Analysis.MomentScaleElimination
import GeometryOfNumbers.Analysis.CarryScaleGeometry

/-! Exact Jacobi covariance for the coherently transported inverse factor,
and inverse-square-root covariance of the EXISTING finite height operator.
No unproved identification with a physical dilation is made. -/
namespace GeometryOfNumbers.Analysis.CarryScale
open FiniteClockHeightLedger
open scoped Matrix
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

private theorem diagonal_inverse (q : ℝ) (hq : q ≠ 0) (N : ℕ) :
    diagonalScale q⁻¹ N * diagonalScale q N = 1 := by
  ext i j
  by_cases h : i = j
  · subst j; simp [diagonalScale, hq]
  · simp [diagonalScale, h]

private theorem transport_diagonal {N : ℕ} (B G D E : Matrix (Fin N) (Fin N) ℝ)
    (hED : E*D = 1) :
    finiteJacobiTransport (B*E) (D*G*D.transpose) = finiteJacobiTransport B G := by
  unfold finiteJacobiTransport
  calc
    _ = B*(E*D)*G*(E*D).transpose*B.transpose := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = _ := by rw [hED]; simp

private theorem transport_smul {N : ℕ} (r s : ℝ) (B G : Matrix (Fin N) (Fin N) ℝ) :
    finiteJacobiTransport (r • B) (s • G) =
      (r*s*r) • finiteJacobiTransport B G := by
  simp [finiteJacobiTransport, Matrix.transpose_smul, smul_smul, mul_assoc]

/-- This is the inverse-factor transport forced by L'=sqrt(a) D L. -/
def scaledInverseFactor {N : ℕ} (a q : ℝ) (B : Matrix (Fin N) (Fin N) ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  (Real.sqrt a)⁻¹ • (B*diagonalScale q⁻¹ N)

private theorem scaled_transport {N : ℕ} (a q s : ℝ) (ha : 0 < a) (hq : q ≠ 0)
    (B G : Matrix (Fin N) (Fin N) ℝ) :
    finiteJacobiTransport (scaledInverseFactor a q B)
        ((a*s) • (diagonalScale q N*G*diagonalScale q N)) =
      s • finiteJacobiTransport B G := by
  unfold scaledInverseFactor
  rw [transport_smul]
  have hD : (diagonalScale q N).transpose = diagonalScale q N := Matrix.diagonal_transpose _
  have he : diagonalScale q N*G*diagonalScale q N =
      diagonalScale q N*G*(diagonalScale q N).transpose := by rw [hD]
  rw [he, transport_diagonal B G _ _ (diagonal_inverse q hq N)]
  have hs : (Real.sqrt a)⁻¹*(a*s)*(Real.sqrt a)⁻¹ = s := by
    have hn := (Real.sqrt_pos.mpr ha).ne'
    have hh := Real.sq_sqrt ha.le
    field_simp
    rw [hh]
  rw [hs]

theorem scaled_whitening {N : ℕ} (a q : ℝ) (ha : 0 < a) (hq : 0 < q)
    (h : ℕ → ℝ) (B : Matrix (Fin N) (Fin N) ℝ)
    (hB : finiteJacobiTransport B (hankelGram h N) = 1) :
    finiteJacobiTransport (scaledInverseFactor a q B)
      (hankelGram (massScaledMoment a q h) N) = 1 := by
  rw [scaled_hankel]
  have ht := scaled_transport a q 1 ha hq.ne' B (hankelGram h N)
  rw [hB] at ht
  simpa only [mul_one, one_smul] using ht

theorem jacobi_scale {N : ℕ} (a q : ℝ) (ha : 0 < a) (hq : 0 < q)
    (h : ℕ → ℝ) (B : Matrix (Fin N) (Fin N) ℝ) :
    finiteJacobiTransport (scaledInverseFactor a q B)
        (shiftedHankel (massScaledMoment a q h) N) =
      q • finiteJacobiTransport B (shiftedHankel h N) := by
  rw [scaled_shifted]
  exact scaled_transport a q q ha hq.ne' B (shiftedHankel h N)

/-- An exact whitening package, with no new invertibility premise. -/
def scaledWhitening (a q : ℝ) (ha : 0 < a) (hq : 0 < q)
    (h : ℕ → ℝ) (N : ℕ) (W : FiniteGramWhitening h N) :
    FiniteGramWhitening (massScaledMoment a q h) N :=
  FiniteGramWhitening.ofIdentity _ _ (scaledInverseFactor a q W.inverseFactor)
    (scaled_whitening a q ha hq h W.inverseFactor W.gram_identity)

theorem jacobi_section_scale (a q : ℝ) (ha : 0 < a) (hq : 0 < q)
    (h : ℕ → ℝ) (N : ℕ) (W : FiniteGramWhitening h N) :
    finiteJacobiSection (massScaledMoment a q h) N (scaledWhitening a q ha hq h N W) =
      q • finiteJacobiSection h N W :=
  jacobi_scale a q ha hq h W.inverseFactor

/-- The abstract mass factor is invisible to this spectral construction. -/
theorem jacobi_mass_blind {N : ℕ} (a b q : ℝ) (ha : 0 < a) (hb : 0 < b) (hq : 0 < q)
    (h : ℕ → ℝ) (B : Matrix (Fin N) (Fin N) ℝ) :
    finiteJacobiTransport (scaledInverseFactor a q B)
        (shiftedHankel (massScaledMoment a q h) N) =
      finiteJacobiTransport (scaledInverseFactor b q B)
        (shiftedHankel (massScaledMoment b q h) N) := by
  rw [jacobi_scale a q ha hq, jacobi_scale b q hb hq]

/-- For the deterministic Cholesky factor, the transported inverse is its
actual matrix inverse wherever the original pivots are positive. -/
theorem cholesky_inverse_scale (h : ℕ → ℝ) (a q : ℝ) (ha : 0 < a) (hq : 0 < q)
    (N : ℕ) (hp : ∀ r < N, 0 < carryPairingPivot (fun i j => h (i+j)) r) :
    (carryPairingCholesky (fun i j => massScaledMoment a q h (i+j)) N)⁻¹ =
      scaledInverseFactor a q (carryPairingCholesky (fun i j => h (i+j)) N)⁻¹ := by
  rw [hankel_cholesky_scale h a q ha hq]
  apply Matrix.inv_eq_left_inv
  let C := carryPairingCholesky (fun i j => h (i+j)) N
  have hc : IsUnit C.det := isUnit_iff_ne_zero.mpr
    (carryPairingCholesky_det_pos _ N hp).ne'
  have hn := (Real.sqrt_pos.mpr ha).ne'
  change scaledInverseFactor a q C⁻¹ * (Real.sqrt a • (diagonalScale q N*C)) = 1
  unfold scaledInverseFactor
  simp only [smul_mul_smul, inv_mul_cancel₀ hn, one_smul]
  calc
    _ = C⁻¹*(diagonalScale q⁻¹ N*diagonalScale q N)*C := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [diagonal_inverse q hq.ne']; simpa using Matrix.nonsing_inv_mul C hc

theorem cholesky_jacobi_scale (h : ℕ → ℝ) (a q : ℝ) (ha : 0 < a) (hq : 0 < q)
    (N : ℕ) (hp : ∀ r < N, 0 < carryPairingPivot (fun i j => h (i+j)) r) :
    finiteJacobiTransport (carryPairingCholesky (fun i j => massScaledMoment a q h (i+j)) N)⁻¹
        (shiftedHankel (massScaledMoment a q h) N) =
      q • finiteJacobiTransport (carryPairingCholesky (fun i j => h (i+j)) N)⁻¹
        (shiftedHankel h N) := by
  rw [cholesky_inverse_scale h a q ha hq N hp]
  exact jacobi_scale a q ha hq h _

/-- Full matrix functional calculus, not merely a scaling of listed eigenvalues. -/
theorem finite_height_scale {N : ℕ} {J : Matrix (Fin N) (Fin N) ℝ}
    (hJ : J.PosDef) (q : ℝ) (hq : 0 < q) :
    finiteHeightOperator (hJ.smul hq) = (Real.sqrt q)⁻¹ • finiteHeightOperator hJ := by
  have hf : ContinuousOn (fun y : ℝ => (Real.sqrt y)⁻¹)
      ((fun y : ℝ => q*y) '' spectrum ℝ J) :=
    ((Matrix.finite_real_spectrum (A := J)).image _).continuousOn _
  have he : (fun y : ℝ => (Real.sqrt (q*y))⁻¹) =
      (fun y : ℝ => (Real.sqrt q)⁻¹*(Real.sqrt y)⁻¹) := by
    funext y; rw [Real.sqrt_mul hq.le, mul_inv]
  calc
    finiteHeightOperator (hJ.smul hq) = cfc (fun y : ℝ => (Real.sqrt y)⁻¹) (q • J) :=
      (Matrix.IsHermitian.cfc_eq (hJ.smul hq).isHermitian _).symm
    _ = cfc (fun y : ℝ => (Real.sqrt (q*y))⁻¹) J :=
      (cfc_comp_const_mul q (fun y : ℝ => (Real.sqrt y)⁻¹) J hf hJ.isHermitian).symm
    _ = (Real.sqrt q)⁻¹ • cfc (fun y : ℝ => (Real.sqrt y)⁻¹) J := by
      rw [he]
      exact cfc_const_mul _ _ J ((Matrix.finite_real_spectrum (A := J)).continuousOn _)
    _ = _ := by rw [Matrix.IsHermitian.cfc_eq hJ.isHermitian]; rfl

/-- The SAME half factor as the geometric depth amplitude, after the
explicit algebraic scaling of J. This is not a physical moment-dilation theorem. -/
theorem finite_height_depth_scale {N : ℕ} {J : Matrix (Fin N) (Fin N) ℝ}
    (hJ : J.PosDef) (b k : ℕ) (hb : 0 < b) :
    finiteHeightOperator (hJ.smul (a := (b:ℝ)^k) (pow_pos (show 0 < (b:ℝ) from Nat.cast_pos.mpr hb) k)) =
      realCriticalAmplitude b k hb • finiteHeightOperator hJ := by
  rw [finite_height_scale hJ ((b:ℝ)^k) (pow_pos (Nat.cast_pos.mpr hb) k),
    amplitude_eq_inverse_sqrt_depth]

end
end GeometryOfNumbers.Analysis.CarryScale
