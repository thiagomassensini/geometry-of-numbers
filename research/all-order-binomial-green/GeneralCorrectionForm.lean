import CanonicalExtraction
import MomentSeparation

namespace CarryBinomialGreen
noncomputable section
set_option autoImplicit false
open scoped BigOperators

/-- The original moment pairing; no sign is part of its definition. -/
def momentBilinear {N M : ℕ} (m : ℕ → ℝ) (s : ℕ)
    (c : Fin N → ℝ) (d : Fin M → ℝ) : ℝ :=
  ∑ i : Fin N, ∑ j : Fin M, c i*d j*m (i.val+j.val+s)

/-- First correction, with all ordered products and the original moments. -/
def correctionBilinear {N M : ℕ} (m : ℕ → ℝ) (s : ℕ)
    (c : Fin N → ℝ) (d : Fin M → ℝ) : ℝ :=
  -∑ i : Fin N, ∑ j : Fin M,
    c i*d j*parityRadialCoefficient s i.val j.val*m (i.val+j.val+s+1)

/-- All orders: a signed polarized relation of three moment pairings.
The two subtracted pairings are not discarded or reinterpreted as norms. -/
theorem correction_bilinear_three_pairings {N M : ℕ} (m : ℕ → ℝ) (s : ℕ)
    (c : Fin N → ℝ) (d : Fin M → ℝ) :
    correctionBilinear m s c d=
      momentBilinear m (s+1) (fun i => triangular (2*i.val+s)*c i)
        (fun j => triangular (2*j.val+s)*d j)-
      momentBilinear m (s+1) (fun i => secondOffset (2*i.val+s)*c i) d-
      momentBilinear m (s+1) c (fun j => secondOffset (2*j.val+s)*d j) := by
  unfold correctionBilinear momentBilinear parityRadialCoefficient
  simp only [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have he : i.val+j.val+s+1=i.val+j.val+(s+1) := by omega
  rw [he]
  ring

/-- Exact finite regression; the generic form is the coefficient of the
already proved native PR88 physical expansion. -/
theorem correction_bilinear_pr88 (m : ℕ → ℝ) (c d : Fin 3 → ℝ) :
    correctionBilinear m 0 c d=momentCorrection m c d := by
  have hc : c 2=c ⟨2,by omega⟩ := rfl
  norm_num [correctionBilinear, parityRadialCoefficient,secondOffset,triangular,
    Fin.sum_univ_succ,momentCorrection,CarryPolarizedFour.crosses]
  ring

theorem correction_bilinear_canonical_pr88 (c d : Fin 3 → ℝ) :
    correctionBilinear CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment 0 c d=
      CarryPolarizedFour.correctionTerm c d := by
  rw [correction_bilinear_pr88,moment_correction_canonical]

end
end CarryBinomialGreen
