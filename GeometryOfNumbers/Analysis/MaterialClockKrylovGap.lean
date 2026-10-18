import GeometryOfNumbers.Analysis.FiniteClockKrylovHankel
import GeometryOfNumbers.Analysis.GreenParsevalMaterialLogOperator
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# A necessary first-column test for the unchanged material logarithmic clock

The nonzero material frequencies are at least log 2 > 1/2. Its first two
squared Krylov energies therefore obey q₂ ≥ q₁/4, for every source, including
sources whose norm was already calibrated. No moment chooses a vector here.
The infinite theorem needs exactly the domains of L and its second application.
-/
noncomputable section
open scoped InnerProductSpace BigOperators lp ENNReal
namespace GeometryOfNumbers.Analysis.MaterialClockKrylovGap
open NativeMaterialClock FiniteClockKrylov FiniteClockJets GreenStateMaterialLog GreenParsevalMaterialLog
set_option autoImplicit false

/-- The zero material frequency is separate; every other address has a gap. -/
theorem material_frequency_gap (n : ℕ) (hn : n ≠ 0) :
    (1/2 : ℝ) ≤ infiniteRealSpectralFrequency n := by
  have hn' : (2 : ℝ) ≤ ((n+1 : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ n+1 by omega)
  have hb := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hn'
  have htwo := Real.log_two_gt_d9
  change (1/2 : ℝ) ≤ Real.log ((n+1 : ℕ) : ℝ)
  linarith

private theorem frequency_nonneg (n : ℕ) : 0 ≤ infiniteRealSpectralFrequency n := by
  apply Real.log_nonneg
  exact_mod_cast (show 1 ≤ n+1 by omega)

private theorem coordinate_gap (n : ℕ) (z : ℂ) :
    (1/4 : ℝ) * ‖(infiniteRealSpectralFrequency n : ℂ) * z‖^2 ≤
      ‖(infiniteRealSpectralFrequency n : ℂ) *
        ((infiniteRealSpectralFrequency n : ℂ) * z)‖^2 := by
  by_cases hn : n = 0
  · subst n
    simp [infiniteRealSpectralFrequency]
  · have hg := material_frequency_gap n hn
    have hs : (1/4 : ℝ) ≤ (infiniteRealSpectralFrequency n)^2 := by nlinarith
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (frequency_nonneg n), mul_pow]
    have hm := mul_le_mul_of_nonneg_right hs
      (mul_nonneg (sq_nonneg (infiniteRealSpectralFrequency n)) (sq_nonneg ‖z‖))
    nlinarith only [hm]

/-- Finite material clock, arbitrary original source: both energies retain all
coordinates of that source and the same operator. -/
theorem finite_clock_energy_gap {M : ℕ} (v : FiniteRealSpectralHilbert M) :
    (1/4 : ℝ) * ‖finiteMaterialClock M v‖^2 ≤
      ‖finiteMaterialClock M (finiteMaterialClock M v)‖^2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  exact coordinate_gap j.val (v j)

/-- The gap is a condition on the FIRST COLUMN of even spectral moments.
The power identities and symmetry are the already-established Krylov bridge. -/
theorem finite_even_first_column_gap {M : ℕ} (v : FiniteRealSpectralHilbert M) :
    (1/4 : ℝ) * finiteClockSpectralMoment v 2 ≤ finiteClockSpectralMoment v 4 := by
  have h1 := finiteClockSpectralMoment_gramRepresentation v 1 1
  have h2 := finiteClockSpectralMoment_gramRepresentation v 2 2
  change finiteClockSpectralMoment v 2 =
    inner ℝ ((finiteMaterialClock M ^ 1) v) ((finiteMaterialClock M ^ 1) v) at h1
  change finiteClockSpectralMoment v 4 =
    inner ℝ ((finiteMaterialClock M ^ 2) v) ((finiteMaterialClock M ^ 2) v) at h2
  rw [real_inner_self_eq_norm_sq] at h1 h2
  rw [h1,h2]
  simpa only [pow_one, pow_two, Module.End.mul_apply] using finite_clock_energy_gap v

/-- The ORIGINAL normalized temporal jets retain their factorials.
The second jet has the fixed 2! denominator; changing phases cannot change
this necessary diagonal inequality. No denormalization is assumed here. -/
theorem finite_normalized_jet_energy_gap {M : ℕ} (v : FiniteRealSpectralHilbert M) :
    (1/16 : ℝ) * ‖normalizedClockJet 1 v‖^2 ≤ ‖normalizedClockJet 2 v‖^2 := by
  have h1 : ‖normalizedClockJet 1 v‖^2 = ‖finiteMaterialClock M v‖^2 := by
    norm_num [normalizedClockJet_eq_krylov, norm_smul]
  have h2 : ‖normalizedClockJet 2 v‖^2 =
      (1/4 : ℝ) * ‖finiteMaterialClock M (finiteMaterialClock M v)‖^2 := by
    norm_num [normalizedClockJet_eq_krylov, norm_smul, norm_mul, norm_inv,
      pow_two, Module.End.mul_apply]
    ring
  rw [h1,h2]
  linarith [finite_clock_energy_gap v]

/-- On the range of the logarithmic clock the material coordinate 1 vanishes.
No mass assumption or assertion about arbitrary ℓ² vectors is needed. -/
theorem infinite_clock_energy_gap (v : infiniteRealSpectralGenerator.domain)
    (hv : infiniteRealSpectralGenerator v ∈ infiniteRealSpectralGenerator.domain) :
    (1/4 : ℝ) * ‖infiniteRealSpectralGenerator v‖^2 ≤
      ‖infiniteRealSpectralGenerator ⟨infiniteRealSpectralGenerator v,hv⟩‖^2 := by
  let y := infiniteRealSpectralGenerator v
  let z := infiniteRealSpectralGenerator ⟨y,hv⟩
  have hs1 := (lp.memℓp y).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  have hs2 := (lp.memℓp z).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  have hn1 := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) y
  have hn2 := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) z
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hs1 hs2 hn1 hn2
  change (1/4 : ℝ) * ‖y‖^2 ≤ ‖z‖^2
  rw [hn1,hn2,← tsum_mul_left]
  exact (hs1.mul_left (1/4 : ℝ)).tsum_le_tsum (fun n => coordinate_gap n (v.val n)) hs2

/-- Isometric transport of the same energies cannot change this obstruction. -/
theorem infinite_clock_isometric_energy_gap {K : Type*} [NormedAddCommGroup K]
    [NormedSpace ℂ K] (P : InfiniteRealSpectralHilbert →ₗᵢ[ℂ] K)
    (v : infiniteRealSpectralGenerator.domain)
    (hv : infiniteRealSpectralGenerator v ∈ infiniteRealSpectralGenerator.domain) :
    (1/4 : ℝ) * ‖P (infiniteRealSpectralGenerator v)‖^2 ≤
      ‖P (infiniteRealSpectralGenerator ⟨infiniteRealSpectralGenerator v,hv⟩)‖^2 := by
  simpa only [P.norm_map] using infinite_clock_energy_gap v hv

/-- The same maximal clock, after the EXISTING material reindexing into
Green State. Both original transported domain conditions remain explicit. -/
theorem green_clock_energy_gap (v : greenStateMaterialLogGenerator.domain)
    (hv : greenStateMaterialLogGenerator v ∈ greenStateMaterialLogGenerator.domain) :
    (1/4 : ℝ) * ‖greenStateMaterialLogGenerator v‖^2 ≤
      ‖greenStateMaterialLogGenerator ⟨greenStateMaterialLogGenerator v,hv⟩‖^2 := by
  let U := nativeLogHilbertEquivGreenState
  let x : nativeLogGenerator.domain := ⟨U.symm v.val,v.prop⟩
  have he : greenStateMaterialLogGenerator v = U (nativeLogGenerator x) := rfl
  have hx : nativeLogGenerator x ∈ nativeLogGenerator.domain := by
    have h := (greenStateMaterialLogGenerator_mem_domain_iff _).mp hv
    rw [he, U.symm_apply_apply] at h
    exact h
  have he2 : greenStateMaterialLogGenerator ⟨greenStateMaterialLogGenerator v,hv⟩ =
      U (nativeLogGenerator ⟨nativeLogGenerator x,hx⟩) := by
    change U (nativeLogGenerator ⟨U.symm (greenStateMaterialLogGenerator v),_⟩) = _
    congr 2
  rw [he2,he,U.norm_map,U.norm_map]
  exact infinite_clock_energy_gap x hx

/-- Canonical Parseval analysis preserves these SAME clocked vectors.
It introduces neither a new clock nor an assertion about raw Green analysis. -/
theorem parseval_clock_energy_gap (v : greenStateMaterialLogGenerator.domain)
    (hv : greenStateMaterialLogGenerator v ∈ greenStateMaterialLogGenerator.domain) :
    (1/4 : ℝ) * ‖greenParsevalAnalysis (greenStateMaterialLogGenerator v)‖^2 ≤
      ‖greenParsevalAnalysis
        (greenStateMaterialLogGenerator ⟨greenStateMaterialLogGenerator v,hv⟩)‖^2 := by
  simpa only [C2GreenWhiteningGenealogy.canonicalGreenAnalysis_norm] using
    green_clock_energy_gap v hv

/-- Two prescribed diagonals violating the material gap cannot come from
this source and its unchanged clock, regardless of all higher orders. -/
theorem infinite_clock_not_matching_two_diagonals (a b : ℝ) (hab : b < a/4) :
    ¬ ∃ (v : infiniteRealSpectralGenerator.domain)
      (hv : infiniteRealSpectralGenerator v ∈ infiniteRealSpectralGenerator.domain),
      ‖infiniteRealSpectralGenerator v‖^2 = a ∧
      ‖infiniteRealSpectralGenerator ⟨infiniteRealSpectralGenerator v,hv⟩‖^2 = b := by
  rintro ⟨v,hv,ha,hb⟩
  have h := infinite_clock_energy_gap v hv
  rw [ha,hb] at h
  linarith

end GeometryOfNumbers.Analysis.MaterialClockKrylovGap
