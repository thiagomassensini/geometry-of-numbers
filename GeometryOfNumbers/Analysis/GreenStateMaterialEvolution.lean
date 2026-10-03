import GeometryOfNumbers.Analysis.GreenParsevalMaterialLogOperator
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! The material logarithmic unitary group on the full Green state.
The logarithmic domain gate is used only for strong differentiation. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Topology lp ENNReal
open Filter
namespace GeometryOfNumbers.Analysis.GreenStateMaterialDynamics
open GreenFrame.Concrete GreenStateMaterialLog GeometryOfNumbers.Analysis.NativeMaterialClock
open C2GlobalGreenBridge C2GreenTemporalMeanCanary GeometryOfNumbers.Analysis

def greenStateMaterialPhase (s : ℝ) (n : PNat) : ℂ :=
  Complex.exp (-(((s * Real.log (n : ℝ) : ℝ) : ℂ) * Complex.I))

theorem greenStateMaterialPhase_eq_native (s : ℝ) (n : PNat) :
    greenStateMaterialPhase s n = infiniteRealSpectralPhase s (natEquivPNat.symm n) := by
  unfold greenStateMaterialPhase infiniteRealSpectralPhase infiniteRealSpectralFrequency
  rw [natEquivPNat_symm_add_one]

@[simp] theorem greenStateMaterialPhase_norm (s : ℝ) (n : PNat) :
    ‖greenStateMaterialPhase s n‖ = 1 := by
  rw [greenStateMaterialPhase_eq_native, norm_infiniteRealSpectralPhase]

@[simp] theorem greenStateMaterialPhase_zero (n : PNat) :
    greenStateMaterialPhase 0 n = 1 := by simp [greenStateMaterialPhase]

theorem greenStateMaterialPhase_add (s r : ℝ) (n : PNat) :
    greenStateMaterialPhase (s+r) n = greenStateMaterialPhase s n * greenStateMaterialPhase r n := by
  simp only [greenStateMaterialPhase_eq_native, infiniteRealSpectralPhase_add]

theorem greenStateMaterialPhase_neg (s : ℝ) (n : PNat) :
    greenStateMaterialPhase (-s) n = (greenStateMaterialPhase s n)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← greenStateMaterialPhase_add]
  simp

theorem greenStateMaterialPhase_eq_phaseFactor (s : ℝ) (n : PNat) :
    greenStateMaterialPhase s n = phaseFactor (-s * Real.log (n : ℝ)) := by
  unfold greenStateMaterialPhase phaseFactor
  congr 1
  push_cast
  ring

/-- Exact conjugation of the preexisting infinite native unitary evolution. -/
def greenStateMaterialEvolution (s : ℝ) : State ≃ₗᵢ[ℂ] State :=
  (nativeLogHilbertEquivGreenState.symm.trans (infiniteRealSpectralEvolution s)).trans
    nativeLogHilbertEquivGreenState

@[simp] theorem greenStateMaterialEvolution_apply (s : ℝ) (f : State) (n : PNat) :
    greenStateMaterialEvolution s f n = greenStateMaterialPhase s n * f n := by
  change nativeLogHilbertEquivGreenState
    (infiniteRealSpectralEvolution s (nativeLogHilbertEquivGreenState.symm f)) n = _
  simp only [nativeLogHilbertEquivGreenState_apply, infiniteRealSpectralEvolution_apply,
    nativeLogHilbertEquivGreenState_symm_apply]
  change infiniteRealSpectralPhase s (natEquivPNat.symm n) * f (natEquivPNat (natEquivPNat.symm n)) = _
  rw [← greenStateMaterialPhase_eq_native, natEquivPNat.apply_symm_apply]

@[simp] theorem greenStateMaterialEvolution_norm (s : ℝ) (f : State) :
    ‖greenStateMaterialEvolution s f‖ = ‖f‖ := (greenStateMaterialEvolution s).norm_map f

@[simp] theorem greenStateMaterialEvolution_zero (f : State) : greenStateMaterialEvolution 0 f = f := by
  ext n
  simp

theorem greenStateMaterialEvolution_add (s r : ℝ) (f : State) :
    greenStateMaterialEvolution (s+r) f = greenStateMaterialEvolution s (greenStateMaterialEvolution r f) := by
  ext n
  simp [greenStateMaterialPhase_add, mul_assoc]

theorem greenStateMaterialEvolution_neg (s : ℝ) :
    greenStateMaterialEvolution (-s) = (greenStateMaterialEvolution s).symm := by
  ext1 f
  apply (greenStateMaterialEvolution s).injective
  rw [← greenStateMaterialEvolution_add]
  simp

theorem greenStateMaterialEvolution_basis (s : ℝ) (n : PNat) :
    greenStateMaterialEvolution s (greenMaterialBasisVector n) =
      greenStateMaterialPhase s n • greenMaterialBasisVector n := by
  ext p
  by_cases h : p = n
  · subst p; simp [greenMaterialBasisVector, lp.single_apply]
  · simp [greenMaterialBasisVector, lp.single_apply, h]

theorem greenStateMaterialEvolution_native_intertwining (s : ℝ) (x : NativeLogHilbert) :
    nativeLogHilbertEquivGreenState (infiniteRealSpectralEvolution s x) =
      greenStateMaterialEvolution s (nativeLogHilbertEquivGreenState x) := by
  simp [greenStateMaterialEvolution]

private theorem state_norm_sq (f : State) : ‖f‖^2 = ∑' n : PNat, ‖f n‖^2 := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) f

private theorem state_square_summable (f : State) : Summable (fun n : PNat => ‖f n‖^2) := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    (lp.memℓp f).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)

/-- Counting-measure dominated convergence in the actual ℓ² norm. -/
private theorem state_tendsto_of_dominated_coordinates {α : Type} {l : Filter α}
    {F : α → State} {g : State} {B : PNat → ℝ} (hB : Summable B)
    (hc : ∀ n, Tendsto (fun a => F a n) l (𝓝 (g n)))
    (hb : ∀ᶠ a in l, ∀ n, ‖F a n - g n‖^2 ≤ B n) : Tendsto F l (𝓝 g) := by
  have ht : Tendsto (fun a => ∑' n : PNat, ‖F a n - g n‖^2) l (𝓝 0) := by
    simpa using (tendsto_tsum_of_dominated_convergence (g := fun _ : PNat => (0 : ℝ)) hB
      (fun n => by simpa using ((hc n).sub (tendsto_const_nhds (x := g n))).norm.pow 2)
      (hb.mono (fun a h n => by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact h n)))
  have ht2 : Tendsto (fun a => ‖F a - g‖^2) l (𝓝 0) := by
    simpa only [state_norm_sq, lp.coeFn_sub, Pi.sub_apply] using ht
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp ht2
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _), Real.sqrt_zero] using hs

theorem greenStateMaterialEvolution_stronglyContinuous (f : State) :
    Continuous (fun s : ℝ => greenStateMaterialEvolution s f) := by
  apply continuous_iff_continuousAt.mpr
  intro r
  apply state_tendsto_of_dominated_coordinates ((state_square_summable f).mul_left 4)
  · intro n
    simp only [greenStateMaterialEvolution_apply]
    exact (show Continuous (fun s : ℝ => greenStateMaterialPhase s n * f n) by
      unfold greenStateMaterialPhase
      fun_prop).continuousAt.tendsto
  · apply Eventually.of_forall
    intro s n
    have h : ‖greenStateMaterialEvolution s f n - greenStateMaterialEvolution r f n‖ ≤ 2 * ‖f n‖ := by
      calc
        _ ≤ ‖greenStateMaterialEvolution s f n‖ + ‖greenStateMaterialEvolution r f n‖ := norm_sub_le _ _
        _ = 2 * ‖f n‖ := by simp; ring
    nlinarith [norm_nonneg (greenStateMaterialEvolution s f n - greenStateMaterialEvolution r f n), norm_nonneg (f n)]

theorem greenStateMaterialEvolution_stronglyContinuous_at_zero (f : State) :
    Tendsto (fun s : ℝ => ‖greenStateMaterialEvolution s f - f‖) (𝓝 0) (𝓝 0) := by
  have h := ((greenStateMaterialEvolution_stronglyContinuous f).continuousAt (x := 0)).tendsto
  exact tendsto_iff_norm_sub_tendsto_zero.mp (by simpa using h)

private theorem phase_sub_one_bound (h : ℝ) (n : PNat) :
    ‖greenStateMaterialPhase h n - 1‖ ≤ ‖h‖ * ‖Real.log (n : ℝ)‖ := by
  have he : greenStateMaterialPhase h n = Complex.exp (Complex.I * ((-h * Real.log (n : ℝ) : ℝ) : ℂ)) := by
    unfold greenStateMaterialPhase; congr 1; push_cast; ring
  rw [he]
  simpa [norm_mul] using (Real.norm_exp_I_mul_ofReal_sub_one_le (x := -h * Real.log (n : ℝ)))

/-- Strong derivative on the maximal logarithmic domain, with the historical minus sign. -/
theorem greenStateMaterialEvolution_hasDerivative_zero (f : State)
    (hf : f ∈ greenStateMaterialLogGenerator.domain) :
    HasDerivAt (fun s : ℝ => greenStateMaterialEvolution s f)
      ((-Complex.I) • greenStateMaterialLogGenerator ⟨f,hf⟩) 0 := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  simp only [zero_add, greenStateMaterialEvolution_zero]
  apply state_tendsto_of_dominated_coordinates
    ((greenStateMaterialLogGenerator_domain_iff_log_moment f).mp hf |>.mul_left 4)
  · intro n
    have hc := (materialLogPhase_hasDerivAt n (f n) 0).tendsto_slope_zero
    simpa only [zero_add, greenStateMaterialEvolution_apply,
      greenStateMaterialPhase_eq_phaseFactor, greenStateMaterialLogGenerator_apply,
      lp.coeFn_smul, Pi.smul_apply, lp.coeFn_sub, Pi.sub_apply, smul_eq_mul, zero_mul, neg_zero, phaseFactor_zero, one_mul,
      Complex.real_smul, ← Complex.ofReal_inv, mul_assoc] using hc
  · apply Eventually.of_forall
    intro h n
    have hq : ‖(h⁻¹ • (greenStateMaterialEvolution h f - f) : State) n‖ ≤
        ‖Real.log (n : ℝ)‖ * ‖f n‖ := by
      simp only [lp.coeFn_smul, Pi.smul_apply, lp.coeFn_sub, Pi.sub_apply, greenStateMaterialEvolution_apply,
        ← sub_one_mul, norm_smul, norm_mul]
      rw [← mul_assoc]
      have hh := mul_le_mul_of_nonneg_left (phase_sub_one_bound h n) (norm_nonneg h⁻¹)
      have hi : ‖h⁻¹‖ * ‖h‖ ≤ 1 := by
        by_cases hz : h = 0
        · simp [hz]
        · rw [norm_inv, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]
      calc
        _ ≤ (‖h⁻¹‖ * (‖h‖ * ‖Real.log (n : ℝ)‖)) * ‖f n‖ := mul_le_mul_of_nonneg_right hh (norm_nonneg _)
        _ = (‖h⁻¹‖ * ‖h‖) * (‖Real.log (n : ℝ)‖ * ‖f n‖) := by ring
        _ ≤ _ := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hi (mul_nonneg (norm_nonneg (Real.log (n : ℝ))) (norm_nonneg (f n)))
    have hd : ‖(((-Complex.I) • greenStateMaterialLogGenerator ⟨f,hf⟩ : State) n)‖ =
        ‖Real.log (n : ℝ)‖ * ‖f n‖ := by
      simp only [lp.coeFn_smul, Pi.smul_apply, greenStateMaterialLogGenerator_apply, norm_smul, norm_neg, Complex.norm_I, norm_mul, Complex.norm_real, one_mul, Real.norm_eq_abs]
    have hb := (norm_sub_le ((h⁻¹ • (greenStateMaterialEvolution h f - f) : State) n)
      (((-Complex.I) • greenStateMaterialLogGenerator ⟨f,hf⟩ : State) n)).trans (add_le_add hq (le_refl _))
    rw [hd] at hb
    have hh : ‖(h⁻¹ • (greenStateMaterialEvolution h f - f) : State) n -
        (((-Complex.I) • greenStateMaterialLogGenerator ⟨f,hf⟩ : State) n)‖ ≤
        2 * (‖Real.log (n : ℝ)‖ * ‖f n‖) := by nlinarith [hb]
    have hs := mul_self_le_mul_self (norm_nonneg _) hh
    simpa only [← pow_two, mul_pow, Real.norm_eq_abs, sq_abs, show (2 : ℝ)^2 = 4 by norm_num] using hs

/-- A strong derivative forces the exact logarithmic ℓ² domain; no extra moment is assumed. -/
theorem greenStateMaterialEvolution_mem_domain_of_hasDerivative_zero (f d : State)
    (hd : HasDerivAt (fun s : ℝ => greenStateMaterialEvolution s f) d 0) :
    f ∈ greenStateMaterialLogGenerator.domain := by
  have hn (n : PNat) : d n = -Complex.I * (Real.log (n : ℝ) : ℂ) * f n := by
    have he := ((lp.evalCLM ℂ (fun _ : PNat => ℂ) 2 n).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hd
    have hc := materialLogPhase_hasDerivAt n (f n) 0
    have he' : HasDerivAt (fun s : ℝ => greenStateMaterialPhase s n * f n) (d n) 0 := by
      simpa only [Function.comp_def, ContinuousLinearMap.coe_restrictScalars', lp.evalCLM, lp.evalₗ,
        LinearMap.coe_mk, AddHom.coe_mk, LinearMap.mkContinuous_apply, greenStateMaterialEvolution_apply] using he
    have hc' : HasDerivAt (fun s : ℝ => greenStateMaterialPhase s n * f n)
        (-Complex.I * (Real.log (n : ℝ) : ℂ) * f n) 0 := by
      simpa only [greenStateMaterialPhase_eq_phaseFactor, zero_mul, neg_zero,
        phaseFactor_zero, one_mul] using hc
    exact he'.unique hc'
  rw [greenStateMaterialLogGenerator_domain_iff_memℓp]
  have he : (fun n : PNat => (Real.log (n : ℝ) : ℂ) * f n) =
      (fun n : PNat => (Complex.I • d : State) n) := by
    funext n
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    rw [hn]
    symm
    calc
      _ = -(Complex.I * Complex.I) * ((Real.log (n : ℝ) : ℂ) * f n) := by ring
      _ = _ := by rw [Complex.I_mul_I]; simp only [neg_neg, one_mul]
  rw [he]
  exact lp.memℓp _

theorem greenStateMaterialEvolution_differentiableAt_zero_iff (f : State) :
    DifferentiableAt ℝ (fun s : ℝ => greenStateMaterialEvolution s f) 0 ↔
      f ∈ greenStateMaterialLogGenerator.domain := by
  constructor
  · intro h
    exact greenStateMaterialEvolution_mem_domain_of_hasDerivative_zero f _ h.hasDerivAt
  · intro h
    exact (greenStateMaterialEvolution_hasDerivative_zero f h).differentiableAt

theorem c2GlobalGreenInput_evolution_add (s t : ℝ) (V : CoreState) :
    greenStateMaterialEvolution s (c2GlobalGreenInputIsometry t V) = c2GlobalGreenInputIsometry (t+s) V := by
  ext n
  rw [greenStateMaterialEvolution_apply, c2Source_phase t V n, c2Source_phase (t+s) V n]
  rw [greenStateMaterialPhase_eq_phaseFactor, ← mul_assoc, ← phaseFactor_add]
  congr 2
  ring

end GeometryOfNumbers.Analysis.GreenStateMaterialDynamics
