import SigmaTransverseJoint
import SigmaTwoPoleModel
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness

/-!
# Conditional separation of a positive zero from the original sigma jets

The source remains the completed characteristic and its original logarithmic response.  The
finite-order zero factorization is obtained from the analytic order theorem.  Any continuation
from that local factorization to the displacement-centered sigma generator is represented by an
explicit hypothesis below; no zero-isolation or continuation claim is silently inserted.
-/

namespace CarrySigmaObstruction

open CarrySelfAdjointOperator CarrySigmaSource
open Filter Topology
open scoped ENNReal
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- The original completed characteristic is analytic at every real height because real
heights lie in its already-certified native height domain. -/
theorem completedNativeF_analyticAt_real (γ : ℝ) :
    AnalyticAt ℂ completedNativeOperatorCharacteristic (γ : ℂ) := by
  apply completedNativeOperatorCharacteristic_analyticAt
  exact ofReal_mem_completedNativeHeightDomain γ

/-- An exact finite analytic order at a positive real zero gives its local factor with
that explicit multiplicity and a nonvanishing analytic quotient. The multiplicity and zero
are hypotheses; the theorem does not assert that a zero is simple or isolated without them. -/
theorem completedNativeF_positive_zero_factorization (γ : ℝ) (m : ℕ)
    (hγ : 0 < γ) (hm : 0 < m)
    (horder : analyticOrderAt completedNativeOperatorCharacteristic (γ : ℂ) = m) :
    0 < γ ∧ completedNativeOperatorCharacteristic (γ : ℂ) = 0 ∧
      ∃ g : ℂ → ℂ,
        AnalyticAt ℂ g (γ : ℂ) ∧ g (γ : ℂ) ≠ 0 ∧
        ∀ᶠ z : ℂ in 𝓝 (γ : ℂ),
          completedNativeOperatorCharacteristic z = (z - (γ : ℂ)) ^ m * g z := by
  have hF := completedNativeF_analyticAt_real γ
  obtain ⟨g, hg, hg0, hfactor⟩ :=
    (hF.analyticOrderAt_eq_natCast).mp horder
  have hzero : completedNativeOperatorCharacteristic (γ : ℂ) = 0 := by
    have heval := hfactor.self_of_nhds
    simpa [hm.ne'] using heval
  exact ⟨hγ, hzero, g, hg, hg0, by simpa [smul_eq_mul] using hfactor⟩

/-- On the punctured neighborhood of a positive zero of exact multiplicity `m`,
the original logarithmic response splits into its forced simple pole and the analytic
logarithmic response of the nonvanishing local factor. -/
theorem completedNativeLogResponse_local_factorization (γ : ℝ) (m : ℕ)
    (hγ : 0 < γ) (hm : 0 < m)
    (horder : analyticOrderAt completedNativeOperatorCharacteristic (γ : ℂ) = m) :
    ∃ g : ℂ → ℂ,
      AnalyticAt ℂ g (γ : ℂ) ∧ g (γ : ℂ) ≠ 0 ∧
      ∀ᶠ z : ℂ in 𝓝[≠] (γ : ℂ),
        completedNativeOperatorCharacteristic z ≠ 0 ∧
        completedNativeLogResponse z =
          -(m : ℂ) / (2 * (z - (γ : ℂ))) - deriv g z / (2 * g z) := by
  obtain ⟨_, _, g, hg, hg0, hfactor⟩ :=
    completedNativeF_positive_zero_factorization γ m hγ hm horder
  let P : ℂ → ℂ := fun z => (z - (γ : ℂ)) ^ m * g z
  have hfact : completedNativeOperatorCharacteristic =ᶠ[𝓝 (γ : ℂ)] P := by
    filter_upwards [hfactor] with z hz
    simpa [P] using hz
  have hderiv := hfact.deriv
  have hgAnalytic := hg.eventually_analyticAt
  have hgNonzero := hg.continuousAt.eventually_ne hg0
  refine ⟨g, hg, hg0, ?_⟩
  filter_upwards [hfact.filter_mono nhdsWithin_le_nhds,
    hderiv.filter_mono nhdsWithin_le_nhds, hgAnalytic.filter_mono nhdsWithin_le_nhds,
    hgNonzero.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with
      z hF hFder hgz hgz0 hpunct
  have hz : z ≠ (γ : ℂ) := by simpa using hpunct
  have hPderiv : deriv P z =
      (m : ℂ) * (z - (γ : ℂ)) ^ (m - 1) * g z +
        (z - (γ : ℂ)) ^ m * deriv g z := by
    change deriv (((fun w : ℂ => w - (γ : ℂ)) ^ m) * g) z = _
    have hsubDiff : DifferentiableAt ℂ (fun w : ℂ => w - (γ : ℂ)) z :=
      differentiableAt_id.sub_const (γ : ℂ)
    rw [deriv_mul (hsubDiff.pow m) hgz.differentiableAt,
      deriv_pow hsubDiff m, deriv_sub_const]
    simp
  have hFderiv : deriv completedNativeOperatorCharacteristic z =
      (m : ℂ) * (z - (γ : ℂ)) ^ (m - 1) * g z +
        (z - (γ : ℂ)) ^ m * deriv g z := by
    rw [hFder, hPderiv]
  have hFne : completedNativeOperatorCharacteristic z ≠ 0 := by
    rw [hF]
    exact mul_ne_zero (pow_ne_zero m (sub_ne_zero.mpr hz)) hgz0
  have hm' : m - 1 + 1 = m := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm.ne')
  refine ⟨hFne, ?_⟩
  rw [completedNativeLogResponse, hFderiv, hF]
  simp only [P]
  field_simp [hz, hgz0, hm']
  rw [← hm', pow_succ]
  rw [hm']
  ring

open CarrySigmaPade

/-- The explicit rational pair model whose Taylor coefficients are the auxiliary two-pole
moments. This is a model term; the source contribution is asserted only under the continuation
hypothesis in `completedSigmaLogJet_zeroPair_conditional_decomposition` below. -/
def sigmaZeroPairRationalModel (m : ℝ) (ζ u : ℂ) : ℂ :=
  ((m : ℂ) / 2) *
    (ζ / (1 - ζ * u) + star ζ / (1 - star ζ * u))

/-- Taylor coefficient sequence of the two-pole rational model. -/
def sigmaZeroPairModelSeries (m : ℝ) (ζ : ℂ) :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ
    (fun n => (twoPoleMoment m ζ n : ℂ))

/-- The real coefficient remainder after subtracting the explicit two-pole model from the
original completed sigma jets. -/
def sigmaZeroPairRemainderMoment (d m : ℝ) (ζ : ℂ) (n : ℕ) : ℝ :=
  completedSigmaLogJet d n - twoPoleMoment m ζ n

/-- Complex Taylor series of the coefficientwise residual, still built from the original jets. -/
def sigmaZeroPairRemainderSeries (d m : ℝ) (ζ : ℂ) :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ
    (fun n => (sigmaZeroPairRemainderMoment d m ζ n : ℂ))

/-- If the original complex sigma generator continues as the two-pole rational model plus
the coefficientwise remainder, uniqueness of Taylor series forces the requested coefficient
decomposition. The continuation radius is stated strictly beyond the model pole radius.

The assumptions `hmodel` and `hdecomp` are the explicit analytic continuation interface: they
are not consequences of a local zero factorization alone. -/
theorem completedSigmaLogJet_zeroPair_conditional_decomposition
    (d m : ℝ) (ζ : ℂ) (hd₁ : -(1 / 2 : ℝ) < d) (hd₂ : d < (1 / 2 : ℝ))
    (hζ : ζ ≠ 0)
    (hmodel : HasFPowerSeriesAt (sigmaZeroPairRationalModel m ζ)
      (sigmaZeroPairModelSeries m ζ) 0)
    (ρ : NNReal)
    (hmodelRadius : ENNReal.ofNNReal (1 / ‖ζ‖₊) < ENNReal.ofNNReal ρ)
    (hremRadius : ENNReal.ofNNReal ρ < (sigmaZeroPairRemainderSeries d m ζ).radius)
    (hdecomp : ∀ᶠ u : ℂ in 𝓝 0,
      completedSigmaLogJetComplexGeneratingFunction d u =
        sigmaZeroPairRationalModel m ζ u +
          (sigmaZeroPairRemainderSeries d m ζ).sum u) :
    ∃ C η : ℝ, 0 < C ∧ 0 < η ∧ η < ‖ζ‖ ∧
      (∀ n, (completedSigmaLogJet d n : ℂ) =
        (twoPoleMoment m ζ n : ℂ) +
          (sigmaZeroPairRemainderMoment d m ζ n : ℂ)) ∧
      ∀ n, |sigmaZeroPairRemainderMoment d m ζ n| ≤ C * η ^ n := by
  let R := sigmaZeroPairRemainderSeries d m ζ
  have hζnorm : 0 < ‖ζ‖ := norm_pos_iff.mpr hζ
  have hρpos : 0 < (ρ : ℝ) := by
    have hζnn : 0 < ‖ζ‖₊ := by exact_mod_cast hζnorm
    have hbase : 0 < (1 / ‖ζ‖₊ : NNReal) := by positivity
    have hmodelRadius' : (1 / ‖ζ‖₊ : NNReal) < ρ :=
      ENNReal.coe_lt_coe.mp hmodelRadius
    exact_mod_cast lt_trans hbase hmodelRadius'
  have hmodelRadiusReal : 1 / ‖ζ‖ < (ρ : ℝ) := by
    have hmodelRadius' : (1 / ‖ζ‖₊ : NNReal) < ρ :=
      ENNReal.coe_lt_coe.mp hmodelRadius
    exact_mod_cast hmodelRadius'
  have hRpos : 0 < R.radius := by
    exact (ENNReal.coe_pos.mpr hρpos).trans hremRadius
  have hsource := completedSigmaLogJetComplexGeneratingFunction_hasFPowerSeriesAt
    d hd₁ hd₂
  have hrem : HasFPowerSeriesAt (fun u : ℂ => R.sum u) R 0 :=
    (R.hasFPowerSeriesOnBall hRpos).hasFPowerSeriesAt
  have hadd := hmodel.add hrem
  have hseriesEq : completedSigmaLogJetComplexSeries d =
      sigmaZeroPairModelSeries m ζ + R :=
    hsource.eq_formalMultilinearSeries_of_eventually hadd hdecomp
  have hcoeff (n : ℕ) :
      (completedSigmaLogJet d n : ℂ) = (twoPoleMoment m ζ n : ℂ) +
        (sigmaZeroPairRemainderMoment d m ζ n : ℂ) := by
    have heval := congrArg (fun S : FormalMultilinearSeries ℂ ℂ ℂ =>
      S n (fun _ : Fin n => (1 : ℂ))) hseriesEq
    simpa [completedSigmaLogJetComplexSeries, sigmaZeroPairModelSeries,
      sigmaZeroPairRemainderSeries, R, FormalMultilinearSeries.ofScalars_apply_eq] using heval
  obtain ⟨C, hCpos, hC⟩ := R.norm_mul_pow_le_of_lt_radius hremRadius
  let η : ℝ := (ρ : ℝ)⁻¹
  have hηpos : 0 < η := by
    dsimp [η]
    exact inv_pos.mpr hρpos
  have hηlt : η < ‖ζ‖ := by
    dsimp [η]
    rw [inv_lt_iff_one_lt_mul₀' hρpos]
    exact (div_lt_iff₀ hζnorm).mp hmodelRadiusReal
  refine ⟨C, η, hCpos, hηpos, hηlt, hcoeff, ?_⟩
  intro n
  have hcoeffNorm : ‖R n‖ = |sigmaZeroPairRemainderMoment d m ζ n| := by
    change ‖sigmaZeroPairRemainderSeries d m ζ n‖ = _
    rw [sigmaZeroPairRemainderSeries, FormalMultilinearSeries.ofScalars_norm,
      Complex.norm_real, Real.norm_eq_abs]
  have hbound := hC n
  rw [hcoeffNorm] at hbound
  have hdiv : |sigmaZeroPairRemainderMoment d m ζ n| ≤ C / (ρ : ℝ) ^ n :=
    (le_div_iff₀ (pow_pos hρpos n)).2 hbound
  simpa [η, div_eq_mul_inv, inv_pow] using hdiv

/-- Combine the proved local factorization at an exact positive zero with the explicit
continuation witness for its shifted conjugate pole pair. The restriction `0 < d < 1/4`
keeps both shifts in the original native analytic domain used by `SigmaZeroObstruction`. -/
theorem completedSigmaLogJet_positive_zero_pair_continuation
    (γ d : ℝ) (mult : ℕ) (ζ : ℂ)
    (hγ : 0 < γ) (hm : 0 < mult)
    (horder : analyticOrderAt completedNativeOperatorCharacteristic (γ : ℂ) = mult)
    (hd : 0 < d) (hdquarter : d < (1 / 4 : ℝ))
    (hζ : ζ = ((γ : ℂ) + Complex.I * (d : ℂ)) ^ (-2 : ℤ))
    (hmodel : HasFPowerSeriesAt (sigmaZeroPairRationalModel (mult : ℝ) ζ)
      (sigmaZeroPairModelSeries (mult : ℝ) ζ) 0)
    (ρ : NNReal)
    (hmodelRadius : ENNReal.ofNNReal (1 / ‖ζ‖₊) < ENNReal.ofNNReal ρ)
    (hremRadius : ENNReal.ofNNReal ρ <
      (sigmaZeroPairRemainderSeries d (mult : ℝ) ζ).radius)
    (hdecomp : ∀ᶠ u : ℂ in 𝓝 0,
      completedSigmaLogJetComplexGeneratingFunction d u =
        sigmaZeroPairRationalModel (mult : ℝ) ζ u +
          (sigmaZeroPairRemainderSeries d (mult : ℝ) ζ).sum u) :
    ζ = ((γ : ℂ) + Complex.I * (d : ℂ)) ^ (-2 : ℤ) ∧
    ∃ g : ℂ → ℂ, ∃ C η : ℝ,
      AnalyticAt ℂ g (γ : ℂ) ∧ g (γ : ℂ) ≠ 0 ∧
      (∀ᶠ z : ℂ in 𝓝[≠] (γ : ℂ),
        completedNativeOperatorCharacteristic z ≠ 0 ∧
        completedNativeLogResponse z =
          -(mult : ℂ) / (2 * (z - (γ : ℂ))) - deriv g z / (2 * g z)) ∧
      0 < C ∧ 0 < η ∧ η < ‖ζ‖ ∧
      (∀ n, (completedSigmaLogJet d n : ℂ) =
        (twoPoleMoment (mult : ℝ) ζ n : ℂ) +
          (sigmaZeroPairRemainderMoment d (mult : ℝ) ζ n : ℂ)) ∧
      ∀ n, |sigmaZeroPairRemainderMoment d (mult : ℝ) ζ n| ≤ C * η ^ n := by
  have hd₁ : -(1 / 2 : ℝ) < d := by linarith
  have hd₂ : d < (1 / 2 : ℝ) := by linarith
  have hnode : (γ : ℂ) + Complex.I * (d : ℂ) ≠ 0 := by
    intro hnode
    have hreal := congrArg Complex.re hnode
    simp at hreal
    linarith
  have hζne : ζ ≠ 0 := by
    rw [hζ]
    exact zpow_ne_zero _ hnode
  obtain ⟨g, hg, hg0, hlocal⟩ :=
    completedNativeLogResponse_local_factorization γ mult hγ hm horder
  obtain ⟨C, η, hC, hη, hηζ, hcoeff, hbound⟩ :=
    completedSigmaLogJet_zeroPair_conditional_decomposition d (mult : ℝ) ζ hd₁ hd₂ hζne
      hmodel ρ hmodelRadius hremRadius hdecomp
  exact ⟨hζ, g, C, η, hg, hg0, hlocal, hC, hη, hηζ, hcoeff, hbound⟩

end
end CarrySigmaObstruction

#print axioms CarrySigmaObstruction.completedNativeF_analyticAt_real
#print axioms CarrySigmaObstruction.completedNativeF_positive_zero_factorization
#print axioms CarrySigmaObstruction.completedNativeLogResponse_local_factorization
#print axioms CarrySigmaObstruction.completedSigmaLogJet_zeroPair_conditional_decomposition
#print axioms CarrySigmaObstruction.completedSigmaLogJet_positive_zero_pair_continuation
