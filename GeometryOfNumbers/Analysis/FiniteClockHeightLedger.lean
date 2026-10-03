import GeometryOfNumbers.Analysis.FiniteMaterialClockJets
import GeometryOfNumbers.Analysis.CanonicalFiniteHeight
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-! A finite coefficient ledger for the recovered historical height code.
The tail, camera factor and Gamma/pi completion germs remain explicit inputs.
The head is certified from material jets. No modern C2 provenance bridge,
numerical tail correctness, or Chebyshev-to-LDL equality is assumed. -/

noncomputable section
open scoped BigOperators
namespace GeometryOfNumbers.Analysis.FiniteClockHeightLedger
open FiniteClockJets

def headSeries {M : ℕ} (weights : Fin M → ℝ) : PowerSeries ℂ :=
  PowerSeries.mk (historicalFiniteHeadCoefficient weights)

def closedResponseSeries {M : ℕ} (weights : Fin M → ℝ)
    (tail cameraFactor completion : PowerSeries ℂ) : PowerSeries ℂ :=
  completion * ((headSeries weights + tail) * cameraFactor⁻¹)

/-- The moment variable is u=t²: Python takes the real part at temporal 2r. -/
def historicalPhi {M : ℕ} (weights : Fin M → ℝ)
    (tail cameraFactor completion : PowerSeries ℂ) (r : ℕ) : ℝ :=
  (PowerSeries.coeff (2*r) (closedResponseSeries weights tail cameraFactor completion)).re

/-- Changing the independently supplied tail can change phi while keeping
the entire material clock/head tower fixed. This prevents erasing that input. -/
theorem externalTail_changes_phi_zero {M : ℕ} (weights : Fin M → ℝ) :
    historicalPhi weights (PowerSeries.C (1 : ℂ)) 1 1 0 =
      historicalPhi weights 0 1 1 0 + 1 := by
  simp [historicalPhi, closedResponseSeries, PowerSeries.coeff_zero_eq_constantCoeff_apply]

theorem closedResponseSeries_camera_quotient {M : ℕ} (weights : Fin M → ℝ)
    (tail cameraFactor completion : PowerSeries ℂ)
    (hB : PowerSeries.constantCoeff cameraFactor ≠ 0) :
    closedResponseSeries weights tail cameraFactor completion * cameraFactor =
      completion * (headSeries weights + tail) := by
  simp only [closedResponseSeries, mul_assoc, PowerSeries.inv_mul_cancel cameraFactor hB,
    mul_one]

/-- Exact coefficient-level completion, with all external germs explicit.
Each phi_r uses a convolution of the clock jets THROUGH order 2r. -/
theorem finiteClockJets_to_phi_with_external_germs {M : ℕ} (weights : Fin M → ℝ)
    (tail cameraFactor completion : PowerSeries ℂ) (r : ℕ) :
    historicalPhi weights tail cameraFactor completion r =
      (∑ p ∈ Finset.antidiagonal (2*r), PowerSeries.coeff p.1 completion *
        ∑ q ∈ Finset.antidiagonal p.2,
          (finiteHeadReadout weights (normalizedClockJet q.1 (historicalInitialState M)) +
            PowerSeries.coeff q.1 tail) * PowerSeries.coeff q.2 cameraFactor⁻¹).re := by
  simp only [historicalPhi, closedResponseSeries, PowerSeries.coeff_mul,
    map_add, headSeries, PowerSeries.coeff_mk, finiteClockJets_to_head]

/-- Finite prefix version: fixed completion inputs, temporal jets through 4d. -/
theorem finiteClockJets_determine_phiPrefix {M M' : ℕ} (w : Fin M → ℝ) (w' : Fin M' → ℝ)
    (tail cameraFactor completion : PowerSeries ℂ) (d : ℕ)
    (hjets : ∀ k, k ≤ 4*d →
      finiteHeadReadout w (normalizedClockJet k (historicalInitialState M)) =
      finiteHeadReadout w' (normalizedClockJet k (historicalInitialState M')))
    (r : ℕ) (hr : r ≤ 2*d) :
    historicalPhi w tail cameraFactor completion r =
      historicalPhi w' tail cameraFactor completion r := by
  rw [finiteClockJets_to_phi_with_external_germs, finiteClockJets_to_phi_with_external_germs]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  congr 1
  apply Finset.sum_congr rfl
  intro q hq
  have hp' := Finset.mem_antidiagonal.mp hp
  have hq' := Finset.mem_antidiagonal.mp hq
  rw [hjets q.1 (by omega)]

/-- Matching every normalized head readout and external germ matches phi.
This is a conditional ledger; it does not identify the historical head with JW_tV. -/
theorem historicalPhi_congr_head {M M' : ℕ} (w : Fin M → ℝ) (w' : Fin M' → ℝ)
    (tail cameraFactor completion : PowerSeries ℂ)
    (hhead : ∀ r, finiteHeadReadout w (normalizedClockJet r (historicalInitialState M)) =
      finiteHeadReadout w' (normalizedClockJet r (historicalInitialState M'))) :
    historicalPhi w tail cameraFactor completion = historicalPhi w' tail cameraFactor completion := by
  have he : headSeries w = headSeries w' := by
    apply PowerSeries.ext
    intro r
    simp only [headSeries, PowerSeries.coeff_mk, finiteClockJets_to_head]
    exact hhead r
  funext r
  simp only [historicalPhi, closedResponseSeries, he]

/-- Exact scalar recurrence used by logarithmic_moments, before rescaling. -/
def finiteLogMoment (phi : ℕ → ℝ) (r : ℕ) : ℝ :=
  (-((r+1 : ℕ) : ℝ) * phi (r+1) -
    ∑ j : Fin r, finiteLogMoment phi j.val * phi (r-j.val)) / phi 0
termination_by r

theorem finiteLogMoment_recurrence (phi : ℕ → ℝ) (r : ℕ) :
    finiteLogMoment phi r =
      (-((r+1 : ℕ) : ℝ) * phi (r+1) -
        ∑ j ∈ Finset.range r, finiteLogMoment phi j * phi (r-j)) / phi 0 := by
  conv_lhs => rw [finiteLogMoment]
  rw [← Fin.sum_univ_eq_sum_range]

theorem finiteLogMoment_isSequence (phi : ℕ → ℝ) (hphi : phi 0 ≠ 0) :
    IsLogDerivativeMomentSequence phi (finiteLogMoment phi) := by
  intro r
  have h := finiteLogMoment_recurrence phi r
  have hm := (eq_div_iff hphi).mp h
  linarith

/-- Reuse the existing uniqueness theorem to match the historical recurrence. -/
theorem finiteLogMoment_eq_existing {phi h : ℕ → ℝ} (hphi : phi 0 ≠ 0)
    (hrel : IsLogDerivativeMomentSequence phi h) : finiteLogMoment phi = h :=
  (finiteLogMoment_isSequence phi hphi).unique hphi hrel

/-- The log-derivative is in u, the even-variable coefficient convention. -/
theorem finiteLogMoment_formal_logDerivative (phi : ℕ → ℝ) (hphi : phi 0 ≠ 0) :
    PowerSeries.mk (finiteLogMoment phi) * PowerSeries.mk phi =
      -(PowerSeries.derivative ℝ (PowerSeries.mk phi)) := by
  apply PowerSeries.ext
  intro r
  simp only [PowerSeries.coeff_mul, PowerSeries.coeff_mk, map_neg,
    PowerSeries.coeff_derivative]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ]
  have hr := finiteLogMoment_isSequence phi hphi r
  simp only [Nat.sub_self, Nat.cast_add, Nat.cast_one] at *
  linarith

theorem finiteLogMoment_formal_quotient (phi : ℕ → ℝ) (hphi : phi 0 ≠ 0) :
    PowerSeries.mk (finiteLogMoment phi) =
      -(PowerSeries.derivative ℝ (PowerSeries.mk phi)) * (PowerSeries.mk phi)⁻¹ := by
  have hc : PowerSeries.constantCoeff (PowerSeries.mk phi) ≠ 0 := by
    simpa only [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk] using hphi
  exact (PowerSeries.eq_mul_inv_iff_mul_eq hc).mpr (finiteLogMoment_formal_logDerivative phi hphi)

/-- Only phi_0,...,phi_(r+1) can affect moment r. -/
theorem finiteLogMoment_triangular {phi psi : ℕ → ℝ} (r : ℕ)
    (hprefix : ∀ k, k ≤ r+1 → phi k = psi k) :
    finiteLogMoment phi r = finiteLogMoment psi r := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
      rw [finiteLogMoment_recurrence, finiteLogMoment_recurrence,
        hprefix 0 (by omega), hprefix (r+1) (by omega)]
      congr 2
      apply Finset.sum_congr rfl
      intro j hj
      have hjr := Finset.mem_range.mp hj
      rw [ih j hjr (fun k hk => hprefix k (by omega)), hprefix (r-j) (by omega)]

def scaledMoment (scale : ℝ) (h : ℕ → ℝ) (r : ℕ) : ℝ := scale ^ r * h r

def historicalScale (phi : ℕ → ℝ) : ℝ := (finiteLogMoment phi 0)⁻¹

def historicalScaledMoment (phi : ℕ → ℝ) : ℕ → ℝ :=
  scaledMoment (historicalScale phi) (finiteLogMoment phi)

theorem historicalScale_pos (phi : ℕ → ℝ) (hh : 0 < finiteLogMoment phi 0) :
    0 < historicalScale phi := inv_pos.mpr hh

/-- The scaled Hankel pair retains exactly the script's c^r convention. -/
theorem scaledMoment_hankel_entries (scale : ℝ) (h : ℕ → ℝ) (d : ℕ) (i j : Fin d) :
    hankelGram (scaledMoment scale h) d i j = scale ^ (i.val+j.val) * h (i.val+j.val) ∧
    shiftedHankel (scaledMoment scale h) d i j =
      scale ^ (i.val+j.val+1) * h (i.val+j.val+1) := ⟨rfl,rfl⟩

private theorem scaledMoment_prefix {phi psi : ℕ → ℝ} (d : ℕ)
    (hp : ∀ k, k ≤ 2*d → phi k = psi k) (k : ℕ) (hk : k < 2*d) :
    historicalScaledMoment phi k = historicalScaledMoment psi k := by
  have hd : 0 < d := by omega
  have hs : historicalScale phi = historicalScale psi := by
    unfold historicalScale
    rw [finiteLogMoment_triangular 0 (fun j hj => hp j (by omega))]
  unfold historicalScaledMoment scaledMoment
  rw [hs, finiteLogMoment_triangular k (fun j hj => hp j (by omega))]

/-- Order d uses phi through 2d, hence temporal head jets through 4d.
The extra tail/factor/completion germs must also be held fixed. -/
theorem finitePhiPrefix_determine_Hankel {phi psi : ℕ → ℝ} (d : ℕ)
    (hp : ∀ k, k ≤ 2*d → phi k = psi k) :
    hankelGram (historicalScaledMoment phi) d = hankelGram (historicalScaledMoment psi) d ∧
    shiftedHankel (historicalScaledMoment phi) d = shiftedHankel (historicalScaledMoment psi) d := by
  constructor <;> ext i j
  · exact scaledMoment_prefix d hp (i.val+j.val) (by omega)
  · exact scaledMoment_prefix d hp (i.val+j.val+1) (by omega)

/-- Exact deterministic canonical downstream section; not a claim that the
Python Chebyshev loop has already been identified with this LDL construction. -/
theorem finitePhiPrefix_determine_JacobiSection {phi psi : ℕ → ℝ} (d : ℕ)
    (hp : ∀ k, k ≤ 2*d → phi k = psi k)
    (hG : (hankelGram (historicalScaledMoment phi) d).PosDef)
    (hG' : (hankelGram (historicalScaledMoment psi) d).PosDef) :
    canonicalFiniteJacobiSection (historicalScaledMoment phi) d hG =
      canonicalFiniteJacobiSection (historicalScaledMoment psi) d hG' := by
  obtain ⟨hg,hk⟩ := finitePhiPrefix_determine_Hankel d hp
  have hb : canonicalLDLInverseFactor hG = canonicalLDLInverseFactor hG' := by
    congr 1
  simp only [canonicalFiniteJacobiSection, finiteJacobiSection,
    canonicalHankelWhitening, finiteJacobiTransport, FiniteGramWhitening.ofIdentity]
  rw [hb,hk]

/-- The correct clock-to-canonical-Jacobi dependency, explicitly relative to
the SAME supplied tail, camera factor and completion germs. -/
theorem finiteClockJets_determine_JacobiSection {M M' : ℕ} (w : Fin M → ℝ) (w' : Fin M' → ℝ)
    (tail cameraFactor completion : PowerSeries ℂ) (d : ℕ)
    (hjets : ∀ k, k ≤ 4*d →
      finiteHeadReadout w (normalizedClockJet k (historicalInitialState M)) =
      finiteHeadReadout w' (normalizedClockJet k (historicalInitialState M')))
    (hG : (hankelGram (historicalScaledMoment
      (historicalPhi w tail cameraFactor completion)) d).PosDef)
    (hG' : (hankelGram (historicalScaledMoment
      (historicalPhi w' tail cameraFactor completion)) d).PosDef) :
    canonicalFiniteJacobiSection
      (historicalScaledMoment (historicalPhi w tail cameraFactor completion)) d hG =
    canonicalFiniteJacobiSection
      (historicalScaledMoment (historicalPhi w' tail cameraFactor completion)) d hG' :=
  finitePhiPrefix_determine_JacobiSection d
    (finiteClockJets_determine_phiPrefix w w' tail cameraFactor completion d hjets) hG hG'

def scaledFiniteHeightOperator {d : ℕ} {J : Matrix (Fin d) (Fin d) ℝ}
    (hJ : J.PosDef) (scale : ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  hJ.isHermitian.cfc (fun y : ℝ => Real.sqrt (scale/y))

theorem scaledFiniteHeightOperator_eigenvector_formula {d : ℕ} {J : Matrix (Fin d) (Fin d) ℝ}
    (hJ : J.PosDef) (scale : ℝ) :
    scaledFiniteHeightOperator hJ scale =
      (hJ.isHermitian.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ) *
        Matrix.diagonal (fun j => Real.sqrt (scale / hJ.isHermitian.eigenvalues j)) *
      (hJ.isHermitian.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ).conjTranspose := by
  simp [scaledFiniteHeightOperator, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply,
    Function.comp_def, Matrix.star_eq_conjTranspose]

theorem scaledFiniteHeightOperator_charpoly {d : ℕ} {J : Matrix (Fin d) (Fin d) ℝ}
    (hJ : J.PosDef) (scale : ℝ) :
    (scaledFiniteHeightOperator hJ scale).charpoly =
      ∏ j : Fin d, (Polynomial.X - Polynomial.C
        (Real.sqrt (scale / hJ.isHermitian.eigenvalues j))) := by
  rw [scaledFiniteHeightOperator, ← Matrix.IsHermitian.cfc_eq hJ.isHermitian]
  exact Matrix.IsHermitian.charpoly_cfc_eq hJ.isHermitian _

theorem scaledFiniteHeight_positive {d : ℕ} {J : Matrix (Fin d) (Fin d) ℝ}
    (hJ : J.PosDef) {scale : ℝ} (hc : 0 < scale) (j : Fin d) :
    0 < Real.sqrt (scale / hJ.isHermitian.eigenvalues j) :=
  Real.sqrt_pos.mpr (div_pos hc (hJ.eigenvalues_pos j))

/-- At scale=1 this is literally the existing finiteHeightOperator. -/
theorem scaledFiniteHeightOperator_one {d : ℕ} {J : Matrix (Fin d) (Fin d) ℝ}
    (hJ : J.PosDef) : scaledFiniteHeightOperator hJ 1 = finiteHeightOperator hJ := by
  unfold scaledFiniteHeightOperator finiteHeightOperator
  congr 1
  funext y
  simp [Real.sqrt_inv]

end GeometryOfNumbers.Analysis.FiniteClockHeightLedger
