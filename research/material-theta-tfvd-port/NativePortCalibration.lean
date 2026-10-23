import GammaJets
import NativeCarryC3Crosswalk.GenuineBracketGreenIdentity
import CarrySelfAdjointOperator.CompletedC3BracketTfvdGreenFactorization

/-! Calibration of the ACTUAL existing finite Genuine Green port, cell by
cell and before its coarse synthesis. The original radial phase is retained
as a parameter-dependent coefficient; it is not differentiated holomorphically.
This does not identify this finite Green projection with the whole TFVD
completion record or with its scalar Wronskian. -/
namespace CarryMaterialTheta
open CPFormal.Analytic.Cp NativeCarryC3Crosswalk NativeCarrySpectralWeyl.Camera
open NativeCarrySpectralWeyl.Boundary
open scoped BigOperators
noncomputable section
set_option autoImplicit false

def heatSample (n : ℕ) (x : ℝ) : ℂ :=
  (Real.exp (-Real.pi*(n : ℝ)^2*x) : ℂ)

theorem finite_address_mellin (N : ℕ) (a : Fin N → ℂ) (r : Fin N → ℕ)
    (hr : ∀ i, 0 < r i) {s : ℂ} (hs : 0 < s.re) :
    mellin (fun x : ℝ => ∑ i : Fin N, a i * heatSample (r i) x) (s/2) =
      Complex.Gammaℝ s * ∑ i : Fin N, a i * dirichletValue s (r i) := by
  have hz (i : Fin N) : (r i : ℝ) ≠ 0 := by exact_mod_cast (hr i).ne'
  have hF : ∀ x ∈ Set.Ioi (0 : ℝ),
      HasSum (fun i : Fin N => if (r i : ℝ) = 0 then 0 else
        a i * (Real.exp (-Real.pi*(r i : ℝ)^2*x) : ℂ))
        (∑ i : Fin N, a i * heatSample (r i) x) := by
    intro x _
    simpa only [heatSample, hz, if_false] using
      hasSum_fintype (fun i : Fin N => a i * heatSample (r i) x)
  have h := hasSum_mellin_pi_mul_sq hs hF (hasSum_fintype _).summable
  have habs (i : Fin N) : ((|(r i : ℝ)| : ℝ) : ℂ) = (r i : ℂ) := by
    rw [abs_of_nonneg (by positivity)]
    norm_cast
  simpa only [tsum_fintype, habs, Finset.mul_sum, mul_div_assoc, dirichletValue,
    Complex.cpow_neg, div_eq_mul_inv, mul_assoc] using h.tsum_eq.symm

theorem heat_difference_mellin (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    {s : ℂ} (hs : 0 < s.re) :
    mellin (fun x : ℝ => heatSample a x - heatSample b x) (s/2) =
      Complex.Gammaℝ s * (dirichletValue s a-dirichletValue s b) := by
  have h := finite_address_mellin 2 ![1,-1] ![a,b]
    (by intro i; fin_cases i <;> simpa using (by assumption : 0 < _)) hs
  simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    one_mul, neg_one_mul, add_neg_cancel_right, sub_eq_add_neg] using h

/-- The destination uses the EXISTING finite two-leg Hilbert carrier. Each
arithmetic cell remains a coordinate; no sum over cells defines the port. -/
def nativeHeatGreenPort (M : ℕ) (s : ℂ) (x : ℝ) : FiniteC3GreenPortCarrier M :=
  (WithLp.toLp 2 (fun i : Fin M => cpPhaseNormalizer 3 s *
    (heatSample (3*(i.val+2)) x - heatSample (3*(i.val+1)) x)),
   WithLp.toLp 2 (fun i : Fin M => heatSample (i.val+2) x-heatSample (i.val+1) x))

def cellwiseMellinPort (M : ℕ) (F : ℝ → FiniteC3GreenPortCarrier M) (s : ℂ) :
    FiniteC3GreenPortCarrier M :=
  (WithLp.toLp 2 (fun i : Fin M => mellin (fun x => (F x).1 i) (s/2)),
   WithLp.toLp 2 (fun i : Fin M => mellin (fun x => (F x).2 i) (s/2)))

/-- Literal finite vector equality to the original Genuine/TFVD Green port,
with its original phase normalizer and material addresses. -/
theorem native_green_port_mellin (M : ℕ) {s : ℂ} (hs : 0 < s.re) :
    cellwiseMellinPort M (nativeHeatGreenPort M s) s =
      Complex.Gammaℝ s • finiteC3GenuineBracketGreenBoundaryPair M s := by
  apply Prod.ext
  · ext i
    change mellin (fun x : ℝ => cpPhaseNormalizer 3 s *
      (heatSample (3*(i.val+2)) x-heatSample (3*(i.val+1)) x)) (s/2) =
        Complex.Gammaℝ s * phaseNormalizedCpGenuineGreenGradient 3 s i.val
    rw [show (fun x : ℝ => cpPhaseNormalizer 3 s *
        (heatSample (3*(i.val+2)) x-heatSample (3*(i.val+1)) x)) =
      (fun x : ℝ => cpPhaseNormalizer 3 s •
        (heatSample (3*(i.val+2)) x-heatSample (3*(i.val+1)) x)) by rfl,
      mellin_const_smul, heat_difference_mellin _ _ (by omega) (by omega) hs]
    rw [phaseNormalizedCpGenuineGreenGradient_eq_phaseNormalizedCpBlockGradient 3 (by norm_num)]
    simp only [
      phaseNormalizedCpBlockGradient, cpBlockGradient_eq_alignedCenterGradient,
      cpAlignedCenterGradient, CPFormal.Genuine.Cp.alignedCenter, smul_eq_mul,
      dirichletTerm, dirichletValue]
    push_cast
    ring_nf
  · ext i
    change mellin (fun x : ℝ => heatSample (i.val+2) x-heatSample (i.val+1) x) (s/2) =
      Complex.Gammaℝ s * positiveDirichletGradient s i.val
    rw [heat_difference_mellin _ _ (by omega) (by omega) hs]
    simp only [positiveDirichletGradient, natDirichletTerm, dirichletTerm,
      dirichletValue]
    push_cast
    rfl

/-- Two independent parameters, pairing the FULL existing finite vectors,
not their coarse scalar sums. The fixed Gamma factors are explicit. -/
theorem native_green_mellin_two_inputs (M : ℕ) {s t : ℂ}
    (hs : 0 < s.re) (ht : 0 < t.re) :
    greenForm (𝕜 := ℂ)
      (cellwiseMellinPort M (nativeHeatGreenPort M s) s)
      (cellwiseMellinPort M (nativeHeatGreenPort M t) t) =
      ((starRingEnd ℂ) (Complex.Gammaℝ s))*Complex.Gammaℝ t *
        greenForm (𝕜 := ℂ) (finiteC3GenuineBracketGreenBoundaryPair M s)
          (finiteC3GenuineBracketGreenBoundaryPair M t) := by
  rw [native_green_port_mellin M hs, native_green_port_mellin M ht]
  simp only [greenForm, Prod.smul_fst, Prod.smul_snd, inner_smul_left, inner_smul_right]
  ring

/-- Direct adapter to the greenPort field of the ORIGINAL enriched TFVD
completion record. The two stored scalar tails are not claimed transported. -/
theorem original_tfvd_green_projection_mellin (M : ℕ) {s : ℂ} (hs : 0 < s.re) :
    cellwiseMellinPort (M*3) (nativeHeatGreenPort (M*3) s) s =
      Complex.Gammaℝ s •
        (CarrySelfAdjointOperator.canonicalC3BracketTfvdCompletionState M s).greenPort := by
  rw [CarrySelfAdjointOperator.canonicalC3BracketTfvdCompletionState_greenPort_eq_bracket]
  exact native_green_port_mellin (M*3) hs

/-- Independent material probe coefficients on BOTH existing Green legs.
These are inputs, not fitted weights or a change of the physical metric. -/
def weightGreenPort (M : ℕ) (left right : Fin M → ℂ)
    (p : FiniteC3GreenPortCarrier M) : FiniteC3GreenPortCarrier M :=
  (WithLp.toLp 2 (fun i : Fin M => left i*p.1 i),
   WithLp.toLp 2 (fun i : Fin M => right i*p.2 i))

theorem cellwise_mellin_weights (M : ℕ) (left right : Fin M → ℂ)
    (F : ℝ → FiniteC3GreenPortCarrier M) (s : ℂ) :
    cellwiseMellinPort M (fun x => weightGreenPort M left right (F x)) s =
      weightGreenPort M left right (cellwiseMellinPort M F s) := by
  apply Prod.ext
  · ext i
    change mellin (fun x : ℝ => left i * (F x).1 i) (s/2) =
      left i * mellin (fun x : ℝ => (F x).1 i) (s/2)
    simpa only [smul_eq_mul] using
      mellin_const_smul (fun x : ℝ => (F x).1 i) (s/2) (left i)
  · ext i
    change mellin (fun x : ℝ => right i * (F x).2 i) (s/2) =
      right i * mellin (fun x : ℝ => (F x).2 i) (s/2)
    simpa only [smul_eq_mul] using
      mellin_const_smul (fun x : ℝ => (F x).2 i) (s/2) (right i)

theorem weighted_native_port_mellin (M : ℕ) (left right : Fin M → ℂ)
    {s : ℂ} (hs : 0 < s.re) :
    cellwiseMellinPort M (fun x => weightGreenPort M left right (nativeHeatGreenPort M s x)) s =
      Complex.Gammaℝ s •
        weightGreenPort M left right (finiteC3GenuineBracketGreenBoundaryPair M s) := by
  rw [cellwise_mellin_weights, native_green_port_mellin M hs]
  apply Prod.ext <;> ext i
  · change left i * (Complex.Gammaℝ s * (finiteC3GenuineBracketGreenBoundaryPair M s).1 i) =
      Complex.Gammaℝ s * (left i * (finiteC3GenuineBracketGreenBoundaryPair M s).1 i)
    ring
  · change right i * (Complex.Gammaℝ s * (finiteC3GenuineBracketGreenBoundaryPair M s).2 i) =
      Complex.Gammaℝ s * (right i * (finiteC3GenuineBracketGreenBoundaryPair M s).2 i)
    ring

/-- Two independent finite material inputs, with each leg and cell still
present when the ORIGINAL physical Green form is applied. -/
theorem weighted_native_two_input_green (M : ℕ)
    (left₁ right₁ left₂ right₂ : Fin M → ℂ) {s t : ℂ}
    (hs : 0 < s.re) (ht : 0 < t.re) :
    greenForm (𝕜 := ℂ)
      (cellwiseMellinPort M (fun x => weightGreenPort M left₁ right₁ (nativeHeatGreenPort M s x)) s)
      (cellwiseMellinPort M (fun x => weightGreenPort M left₂ right₂ (nativeHeatGreenPort M t x)) t) =
      ((starRingEnd ℂ) (Complex.Gammaℝ s))*Complex.Gammaℝ t *
        greenForm (𝕜 := ℂ)
          (weightGreenPort M left₁ right₁ (finiteC3GenuineBracketGreenBoundaryPair M s))
          (weightGreenPort M left₂ right₂ (finiteC3GenuineBracketGreenBoundaryPair M t)) := by
  rw [weighted_native_port_mellin M left₁ right₁ hs, weighted_native_port_mellin M left₂ right₂ ht]
  simp only [greenForm, Prod.smul_fst, Prod.smul_snd, inner_smul_left, inner_smul_right]
  ring

end
end CarryMaterialTheta
