import SigmaNeighborhood
import Mathlib.Tactic

/-!
# Signed finite sigma pencils

The metric is the original two by two window of `sigmaMatrix`.  No positivity
assumption is used: invertibility alone defines the Galerkin pencil.
-/

open scoped Matrix

namespace CarrySigmaPade

open CarryMovingSigma
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- The original two-moment sigma window. -/
def sigmaPencilGram (d : ℝ) (s : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  sigmaMatrix d s 2

/-- The next original sigma window, shifted by one moment. -/
def sigmaPencilShifted (d : ℝ) (s : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  sigmaMatrix d (s + 1) 2

/-- Signed Galerkin multiplication `A = G⁻¹ K`, defined before imposing
any positivity condition on the original sigma window. -/
def sigmaPencilOperator (d : ℝ) (s : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (sigmaPencilGram d s)⁻¹ * sigmaPencilShifted d s

/-- For every invertible original window, `G A = K = Aᵀ G`.  Only
`IsUnit G` is assumed; the signed metric may be indefinite. -/
theorem sigmaPencil_metricSelfAdjoint (d : ℝ) (s : ℕ)
    (hG : IsUnit (sigmaPencilGram d s)) :
    sigmaPencilGram d s * sigmaPencilOperator d s = sigmaPencilShifted d s ∧
      (sigmaPencilOperator d s).transpose * sigmaPencilGram d s =
        sigmaPencilShifted d s := by
  have hGsym : (sigmaPencilGram d s).transpose = sigmaPencilGram d s := by
    exact sigma_matrix_symm d s 2
  have hKsym : (sigmaPencilShifted d s).transpose = sigmaPencilShifted d s := by
    exact sigma_matrix_symm d (s + 1) 2
  have hleft : sigmaPencilGram d s * sigmaPencilOperator d s =
      sigmaPencilShifted d s := by
    letI : Invertible (sigmaPencilGram d s) := hG.invertible
    change sigmaPencilGram d s *
      ((sigmaPencilGram d s)⁻¹ * sigmaPencilShifted d s) = _
    rw [← Matrix.mul_assoc, Matrix.mul_inv_of_invertible, Matrix.one_mul]
  have htranspose := congrArg Matrix.transpose hleft
  rw [Matrix.transpose_mul, hGsym, hKsym] at htranspose
  exact ⟨hleft, htranspose⟩

/-- A generalized eigenvector of two Hermitian matrices is isotropic for the
metric whenever its generalized eigenvalue is nonreal.  This does not claim
that the vector lies in the kernel of the metric. -/
theorem hermitian_generalizedEigenvector_isotropic
    {N : ℕ} (G K : Matrix (Fin N) (Fin N) ℂ)
    (hG : G.IsHermitian) (hK : K.IsHermitian)
    (v : Fin N → ℂ) (eigenvalue : ℂ)
    (heigen : K *ᵥ v = eigenvalue • (G *ᵥ v))
    (hEigenvalueIm : eigenvalue.im ≠ 0) :
    star v ⬝ᵥ (G *ᵥ v) = 0 := by
  let qG : ℂ := star v ⬝ᵥ (G *ᵥ v)
  let qK : ℂ := star v ⬝ᵥ (K *ᵥ v)
  have hrelation : qK = eigenvalue * qG := by
    dsimp [qK, qG]
    rw [heigen]
    simp only [dotProduct_smul, smul_eq_mul]
  have hGim : qG.im = 0 := by
    simpa [qG] using hG.im_star_dotProduct_mulVec_self v
  have hKim : qK.im = 0 := by
    simpa [qK] using hK.im_star_dotProduct_mulVec_self v
  have hmul : eigenvalue.im * qG.re = 0 := by
    have him := congrArg Complex.im hrelation
    simpa [Complex.mul_im, hKim, hGim] using him.symm
  have hreal : qG.re = 0 :=
    (mul_eq_zero.mp hmul).resolve_left hEigenvalueIm
  apply Complex.ext
  · exact hreal
  · exact hGim

#print axioms sigmaPencil_metricSelfAdjoint
#print axioms hermitian_generalizedEigenvector_isotropic

end
end CarrySigmaPade
