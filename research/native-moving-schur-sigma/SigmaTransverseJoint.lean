import SigmaTransverseAllOrder
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.Liouville

/-!
# Joint displacement regularity for the original transverse sigma source

This module starts the missing displacement-section argument. It keeps the original
completed sigma jets and expresses finite transverse derivatives through the original
logarithmic response `Q = -F'/(2F)`.
-/

namespace CarrySigmaObstruction
open CarrySelfAdjointOperator CarrySigmaSource
open CPFormal.Analytic.Cp
open Filter Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000

private theorem sigmaJoint_analyticAt_iteratedDeriv
    (f : ℂ → ℂ) (z : ℂ) (hf : AnalyticAt ℂ f z) (n : ℕ) :
    AnalyticAt ℂ (iteratedDeriv n f) z := by
  induction n with
  | zero => simpa [iteratedDeriv_zero] using hf
  | succ n ih =>
      rw [iteratedDeriv_succ]
      exact ih.deriv

private theorem sigmaJoint_affine_path_analyticAt
    (f : ℂ → ℂ) (a b : ℂ) (x : ℝ)
    (hf : AnalyticAt ℂ f (a + b * (x : ℂ))) :
    AnalyticAt ℝ (fun y : ℝ => f (a + b * (y : ℂ))) x := by
  have hpath : AnalyticAt ℝ (fun y : ℝ => a + b * (y : ℂ)) x := by
    exact analyticAt_const.add (analyticAt_const.mul (Complex.ofRealCLM.analyticAt x))
  exact AnalyticAt.comp (f := fun y : ℝ => a + b * (y : ℂ))
    hf.restrictScalars hpath

private theorem sigmaJoint_affine_path_deriv
    (f : ℂ → ℂ) (a b : ℂ) (x : ℝ)
    (hf : AnalyticAt ℂ f (a + b * (x : ℂ))) :
    deriv (fun y : ℝ => f (a + b * (y : ℂ))) x =
      b * deriv f (a + b * (x : ℂ)) := by
  have hinner : HasDerivAt (fun z : ℂ => a + b * z) b (x : ℂ) := by
    simpa [mul_comm, add_comm] using
      ((hasDerivAt_id (x : ℂ)).const_mul b).const_add a
  have hpath := hinner.comp_ofReal
  calc
    deriv (fun y : ℝ => f (a + b * (y : ℂ))) x =
        deriv f (a + b * (x : ℂ)) *
          deriv (fun y : ℝ => a + b * (y : ℂ)) x := by
          simpa only [Function.comp_def] using
            deriv_comp_of_eq (x := x) (y := a + b * (x : ℂ))
              hf.differentiableAt hpath.differentiableAt rfl
    _ = b * deriv f (a + b * (x : ℂ)) := by
          rw [hpath.deriv]
          ring

private theorem sigmaJoint_affine_path_iteratedDeriv
    (n : ℕ) (f : ℂ → ℂ) (a b : ℂ) (x : ℝ)
    (hf : AnalyticAt ℂ f (a + b * (x : ℂ))) :
    iteratedDeriv n (fun y : ℝ => f (a + b * (y : ℂ))) x =
      b ^ n * iteratedDeriv n f (a + b * (x : ℂ)) := by
  induction n generalizing f a b x with
  | zero => simp [iteratedDeriv_zero]
  | succ n ih =>
      have hpath : ContinuousAt (fun y : ℝ => a + b * (y : ℂ)) x := by fun_prop
      have hnear : ∀ᶠ y : ℝ in 𝓝 x, AnalyticAt ℂ f (a + b * (y : ℂ)) :=
        hpath.tendsto hf.eventually_analyticAt
      have hfirst :
          (fun y : ℝ => deriv (fun z : ℝ => f (a + b * (z : ℂ))) y) =ᶠ[𝓝 x]
            (fun y : ℝ => b * deriv f (a + b * (y : ℂ))) := by
        filter_upwards [hnear] with y hy
        exact sigmaJoint_affine_path_deriv f a b y hy
      have hiter := Filter.EventuallyEq.iteratedDeriv_eq n hfirst
      rw [iteratedDeriv_succ']
      calc
        iteratedDeriv n (fun y : ℝ => deriv (fun z : ℝ => f (a + b * (z : ℂ))) y) x =
            iteratedDeriv n (fun y : ℝ => b * deriv f (a + b * (y : ℂ))) x := hiter
        _ = b * iteratedDeriv n (fun y : ℝ => deriv f (a + b * (y : ℂ))) x := by
            rw [iteratedDeriv_const_mul_field]
        _ = b * (b ^ n * iteratedDeriv n (deriv f) (a + b * (x : ℂ))) := by
            rw [ih (deriv f) a b x hf.deriv]
        _ = b ^ (n + 1) * iteratedDeriv (n + 1) f (a + b * (x : ℂ)) := by
            rw [iteratedDeriv_succ']
            ring

private theorem sigmaJoint_iteratedDeriv_realPart_restrict
    (f : ℂ → ℂ) (x : ℝ) (n : ℕ)
    (hf : AnalyticAt ℂ f (x : ℂ)) :
    iteratedDeriv n (fun y : ℝ => (f (y : ℂ)).re) x =
      (iteratedDeriv n f (x : ℂ)).re := by
  induction n generalizing f x with
  | zero => simp [iteratedDeriv_zero]
  | succ n ih =>
      have hpath : ContinuousAt (fun y : ℝ => (y : ℂ)) x := by fun_prop
      have hnear : ∀ᶠ y : ℝ in 𝓝 x, AnalyticAt ℂ f (y : ℂ) :=
        hpath.tendsto hf.eventually_analyticAt
      have heq :
          (fun y : ℝ => iteratedDeriv n (fun z : ℝ => (f (z : ℂ)).re) y) =ᶠ[𝓝 x]
            (fun y : ℝ => (iteratedDeriv n f (y : ℂ)).re) := by
        filter_upwards [hnear] with y hy
        exact ih f y hy
      have hderivEq := heq.deriv_eq
      have hfn : AnalyticAt ℂ (iteratedDeriv n f) (x : ℂ) :=
        sigmaJoint_analyticAt_iteratedDeriv f _ hf n
      have hrealDeriv := (hfn.differentiableAt.hasDerivAt).real_of_complex
      calc
        iteratedDeriv (n + 1) (fun y : ℝ => (f (y : ℂ)).re) x =
            deriv (iteratedDeriv n (fun y : ℝ => (f (y : ℂ)).re)) x := by
              rw [iteratedDeriv_succ]
        _ = deriv (fun y : ℝ => (iteratedDeriv n f (y : ℂ)).re) x := hderivEq
        _ = (deriv (iteratedDeriv n f) (x : ℂ)).re := by
              simpa only [Function.comp_def] using hrealDeriv.deriv
        _ = (iteratedDeriv (n + 1) f (x : ℂ)).re := by
              rw [iteratedDeriv_succ]

/-- The complex transverse mean is analytic as a function of the longitudinal variable at
the center whenever its two response values are analytic. -/
private theorem sigmaJoint_mean_analyticAt_t
    (Q : ℂ → ℂ) (d : ℝ)
    (hminus : AnalyticAt ℂ Q ((0 : ℂ) - Complex.I * (d : ℂ)))
    (hplus : AnalyticAt ℂ Q ((0 : ℂ) + Complex.I * (d : ℂ))) :
    AnalyticAt ℂ (fun z : ℂ => sigmaTransverseMean Q z d) 0 := by
  have hminusPath : AnalyticAt ℂ (fun z : ℂ => Q (z - Complex.I * (d : ℂ))) 0 := by
    exact AnalyticAt.comp (f := fun z : ℂ => z - Complex.I * (d : ℂ))
      hminus (analyticAt_id.sub analyticAt_const)
  have hplusPath : AnalyticAt ℂ (fun z : ℂ => Q (z + Complex.I * (d : ℂ))) 0 := by
    exact AnalyticAt.comp (f := fun z : ℂ => z + Complex.I * (d : ℂ))
      hplus (analyticAt_id.add analyticAt_const)
  have heq : (fun z : ℂ => sigmaTransverseMean Q z d) =
      (fun z : ℂ => (1 / 2 : ℂ) *
        (Q (z - Complex.I * (d : ℂ)) + Q (z + Complex.I * (d : ℂ)))) := by
    funext z
    simp [sigmaTransverseMean]
    ring
  rw [heq]
  exact analyticAt_const.mul (hminusPath.add hplusPath)

private theorem sigmaJoint_mean_analyticAt_real_t
    (Q : ℂ → ℂ) (d t : ℝ)
    (hminus : AnalyticAt ℂ Q ((t : ℂ) - Complex.I * (d : ℂ)))
    (hplus : AnalyticAt ℂ Q ((t : ℂ) + Complex.I * (d : ℂ))) :
    AnalyticAt ℝ (fun x : ℝ => sigmaTransverseMean Q (x : ℂ) d) t := by
  let am : ℂ := -(Complex.I * (d : ℂ))
  let ap : ℂ := Complex.I * (d : ℂ)
  let qm : ℝ → ℂ := fun x => Q (am + 1 * (x : ℂ))
  let qp : ℝ → ℂ := fun x => Q (ap + 1 * (x : ℂ))
  have hminusPath : AnalyticAt ℂ Q (am + 1 * (t : ℂ)) := by
    dsimp [am]
    convert hminus using 1
    ring_nf
  have hplusPath : AnalyticAt ℂ Q (ap + 1 * (t : ℂ)) := by
    dsimp [ap]
    convert hplus using 1
    ring_nf
  have hminusAnalytic : AnalyticAt ℝ qm t :=
    sigmaJoint_affine_path_analyticAt Q am 1 t hminusPath
  have hplusAnalytic : AnalyticAt ℝ qp t :=
    sigmaJoint_affine_path_analyticAt Q ap 1 t hplusPath
  have hmean : (fun x : ℝ => sigmaTransverseMean Q (x : ℂ) d) =
      (fun x : ℝ => (1 / 2 : ℂ) * (qm x + qp x)) := by
    funext x
    simp [sigmaTransverseMean, qm, qp, am, ap]
    ring
  rw [hmean]
  exact analyticAt_const.mul (hminusAnalytic.add hplusAnalytic)

/-- The `k`th longitudinal derivative of the transverse mean at the center. -/
def sigmaTransverseMeanTDerivative (Q : ℂ → ℂ) (d : ℝ) (k : ℕ) : ℂ :=
  iteratedDeriv k (fun t : ℝ => sigmaTransverseMeanReal Q t d) 0

private theorem sigmaJoint_mean_t_iteratedDeriv
    (Q : ℂ → ℂ) (d : ℝ) (k : ℕ)
    (hminus : AnalyticAt ℂ Q ((0 : ℂ) - Complex.I * (d : ℂ)))
    (hplus : AnalyticAt ℂ Q ((0 : ℂ) + Complex.I * (d : ℂ))) :
    sigmaTransverseMeanTDerivative Q d k =
      (1 / 2 : ℂ) *
        (iteratedDeriv k Q ((0 : ℂ) - Complex.I * (d : ℂ)) +
          iteratedDeriv k Q ((0 : ℂ) + Complex.I * (d : ℂ))) := by
  let am : ℂ := -(Complex.I * (d : ℂ))
  let ap : ℂ := Complex.I * (d : ℂ)
  let qm : ℝ → ℂ := fun t => Q (am + 1 * (t : ℂ))
  let qp : ℝ → ℂ := fun t => Q (ap + 1 * (t : ℂ))
  have hminusPath : AnalyticAt ℂ Q (am + 1 * (0 : ℂ)) := by
    simpa [am] using hminus
  have hplusPath : AnalyticAt ℂ Q (ap + 1 * (0 : ℂ)) := by
    simpa [ap] using hplus
  have hminusAnalytic : AnalyticAt ℝ qm 0 :=
    sigmaJoint_affine_path_analyticAt Q am 1 0 hminusPath
  have hplusAnalytic : AnalyticAt ℝ qp 0 :=
    sigmaJoint_affine_path_analyticAt Q ap 1 0 hplusPath
  have hmean : (fun t : ℝ => sigmaTransverseMeanReal Q t d) =
      (fun t : ℝ => (1 / 2 : ℂ) * (qm t + qp t)) := by
    funext t
    simp [sigmaTransverseMeanReal, sigmaTransverseMean, qm, qp, am, ap]
    ring
  rw [sigmaTransverseMeanTDerivative, hmean,
    iteratedDeriv_const_mul_field]
  have hsum := iteratedDeriv_add (n := k) (f := qm) (g := qp) (x := 0)
    hminusAnalytic.contDiffAt hplusAnalytic.contDiffAt
  have hsum' : iteratedDeriv k (fun t : ℝ => qm t + qp t) 0 =
      iteratedDeriv k qm 0 + iteratedDeriv k qp 0 := by
    change iteratedDeriv k (qm + qp) 0 = _
    exact hsum
  rw [hsum',
    sigmaJoint_affine_path_iteratedDeriv k Q am 1 0 hminusPath,
    sigmaJoint_affine_path_iteratedDeriv k Q ap 1 0 hplusPath]
  simp only [one_pow]
  simp [am, ap]

/-- Every finite longitudinal derivative of the original transverse mean is analytic in the
displacement wherever the two characteristic factors are nonzero. Its formula is a finite
sum of derivatives of the original `Q` evaluated at `± i d`. -/
theorem sigmaTransverseMeanTDerivative_analyticAt
    (Q : ℂ → ℂ) (d : ℝ) (k : ℕ)
    (hminus : AnalyticAt ℂ Q ((0 : ℂ) - Complex.I * (d : ℂ)))
    (hplus : AnalyticAt ℂ Q ((0 : ℂ) + Complex.I * (d : ℂ))) :
    AnalyticAt ℝ (fun y : ℝ => sigmaTransverseMeanTDerivative Q y k) d := by
  let Qk : ℂ → ℂ := iteratedDeriv k Q
  have hQkm : AnalyticAt ℂ Qk ((0 : ℂ) - Complex.I * (d : ℂ)) :=
    sigmaJoint_analyticAt_iteratedDeriv Q _ hminus k
  have hQkp : AnalyticAt ℂ Qk ((0 : ℂ) + Complex.I * (d : ℂ)) :=
    sigmaJoint_analyticAt_iteratedDeriv Q _ hplus k
  have hpathm : AnalyticAt ℝ (fun y : ℝ => Qk (0 + (-Complex.I) * (y : ℂ))) d := by
    apply sigmaJoint_affine_path_analyticAt Qk 0 (-Complex.I) d
    simpa [Qk] using hQkm
  have hpathp : AnalyticAt ℝ (fun y : ℝ => Qk (0 + Complex.I * (y : ℂ))) d := by
    apply sigmaJoint_affine_path_analyticAt Qk 0 Complex.I d
    simpa [Qk] using hQkp
  have hexpr : AnalyticAt ℝ
      (fun y : ℝ => (1 / 2 : ℂ) *
        (Qk (0 + (-Complex.I) * (y : ℂ)) + Qk (0 + Complex.I * (y : ℂ)))) d := by
    exact (analyticAt_const.mul (hpathm.add hpathp))
  have hmapm : ContinuousAt (fun y : ℝ =>
      (0 : ℂ) - Complex.I * (y : ℂ)) d := by fun_prop
  have hmapp : ContinuousAt (fun y : ℝ =>
      (0 : ℂ) + Complex.I * (y : ℂ)) d := by fun_prop
  have hnearM : ∀ᶠ y : ℝ in 𝓝 d,
      AnalyticAt ℂ Q ((0 : ℂ) - Complex.I * (y : ℂ)) :=
    hmapm.tendsto hminus.eventually_analyticAt
  have hnearP : ∀ᶠ y : ℝ in 𝓝 d,
      AnalyticAt ℂ Q ((0 : ℂ) + Complex.I * (y : ℂ)) :=
    hmapp.tendsto hplus.eventually_analyticAt
  have heq : (fun y : ℝ => sigmaTransverseMeanTDerivative Q y k) =ᶠ[𝓝 d]
      (fun y : ℝ => (1 / 2 : ℂ) *
        (Qk (0 + (-Complex.I) * (y : ℂ)) + Qk (0 + Complex.I * (y : ℂ)))) := by
    filter_upwards [hnearM, hnearP] with y hym hyp
    simpa [Qk] using sigmaJoint_mean_t_iteratedDeriv Q y k hym hyp
  exact hexpr.congr heq.symm

private theorem sigmaJoint_mean_complex_iteratedDeriv
    (Q : ℂ → ℂ) (d : ℝ) (k : ℕ)
    (hminus : AnalyticAt ℂ Q ((0 : ℂ) - Complex.I * (d : ℂ)))
    (hplus : AnalyticAt ℂ Q ((0 : ℂ) + Complex.I * (d : ℂ))) :
    iteratedDeriv k (fun z : ℂ => sigmaTransverseMean Q z d) 0 =
      (1 / 2 : ℂ) *
        (iteratedDeriv k Q ((0 : ℂ) - Complex.I * (d : ℂ)) +
          iteratedDeriv k Q ((0 : ℂ) + Complex.I * (d : ℂ))) := by
  let am : ℂ := -(Complex.I * (d : ℂ))
  let ap : ℂ := Complex.I * (d : ℂ)
  let qm : ℂ → ℂ := fun z => Q (am + z)
  let qp : ℂ → ℂ := fun z => Q (ap + z)
  have hminusPath : AnalyticAt ℂ Q (am + 0) := by simpa [am] using hminus
  have hplusPath : AnalyticAt ℂ Q (ap + 0) := by simpa [ap] using hplus
  have hminusAnalytic : AnalyticAt ℂ qm 0 := by
    exact AnalyticAt.comp (f := fun z : ℂ => am + z) hminusPath
      (analyticAt_const.add analyticAt_id)
  have hplusAnalytic : AnalyticAt ℂ qp 0 := by
    exact AnalyticAt.comp (f := fun z : ℂ => ap + z) hplusPath
      (analyticAt_const.add analyticAt_id)
  have hmean : (fun z : ℂ => sigmaTransverseMean Q z d) =
      (fun z : ℂ => (1 / 2 : ℂ) * (qm z + qp z)) := by
    funext z
    simp [sigmaTransverseMean, qm, qp, am, ap]
    ring
  rw [hmean, iteratedDeriv_const_mul_field]
  have hsum := iteratedDeriv_add (n := k) (f := qm) (g := qp) (x := 0)
    hminusAnalytic.contDiffAt hplusAnalytic.contDiffAt
  rw [show (fun z : ℂ => qm z + qp z) = qm + qp by rfl, hsum]
  have hqm : iteratedDeriv k qm 0 = iteratedDeriv k Q am := by
    have h := congrFun (iteratedDeriv_comp_const_add k Q am) 0
    simpa [qm] using h
  have hqp : iteratedDeriv k qp 0 = iteratedDeriv k Q ap := by
    have h := congrFun (iteratedDeriv_comp_const_add k Q ap) 0
    simpa [qp] using h
  rw [hqm, hqp]
  simp [am, ap]

private theorem sigmaJoint_mean_TDerivative_eq_complex
    (Q : ℂ → ℂ) (d : ℝ) (k : ℕ)
    (hminus : AnalyticAt ℂ Q ((0 : ℂ) - Complex.I * (d : ℂ)))
    (hplus : AnalyticAt ℂ Q ((0 : ℂ) + Complex.I * (d : ℂ))) :
    sigmaTransverseMeanTDerivative Q d k =
      iteratedDeriv k (fun z : ℂ => sigmaTransverseMean Q z d) 0 := by
  rw [sigmaJoint_mean_t_iteratedDeriv Q d k hminus hplus,
    sigmaJoint_mean_complex_iteratedDeriv Q d k hminus hplus]

/-- The original characteristic's logarithmic response is analytic at both imaginary
points used by an admissible displacement. Nonvanishing comes from the original positive
sigma density, with the conjugate response supplying the opposite point. -/
theorem completedNativeLogResponse_analyticAt_imaginary (d : ℝ)
    (hd₁ : -(1 / 2 : ℝ) < d) (hd₂ : d < (1 / 2 : ℝ)) :
    AnalyticAt ℂ completedNativeLogResponse
        ((0 : ℂ) - Complex.I * (d : ℂ)) ∧
    AnalyticAt ℂ completedNativeLogResponse
        ((0 : ℂ) + Complex.I * (d : ℂ)) := by
  let F : ℂ → ℂ := completedNativeOperatorCharacteristic
  let zm : ℂ := (0 : ℂ) - Complex.I * (d : ℂ)
  let zp : ℂ := (0 : ℂ) + Complex.I * (d : ℂ)
  have hdm : zm ∈ completedNativeHeightDomain := by
    show operatorHeightParameter zm ∈ genuineCriticalStrip
    have heq : zm = displacedHeight d 0 := by
      simp [zm, displacedHeight]
    rw [heq]
    exact displacedHeight_strip d 0 hd₁ hd₂
  have hdp : zp ∈ completedNativeHeightDomain := by
    show operatorHeightParameter zp ∈ genuineCriticalStrip
    have heq : zp = displacedHeight (-d) 0 := by
      simp [zp, displacedHeight]
    rw [heq]
    exact displacedHeight_strip (-d) 0 (by linarith) (by linarith)
  have hFm : AnalyticAt ℂ F zm := by
    dsimp [F]
    exact completedNativeOperatorCharacteristic_analyticAt hdm
  have hFp : AnalyticAt ℂ F zp := by
    dsimp [F]
    exact completedNativeOperatorCharacteristic_analyticAt hdp
  have hrm : completedSigmaResponse d 0 ≠ 0 := by
    intro hz
    have hp := completedSigmaDensity_zero_pos d hd₁ hd₂
    unfold completedSigmaDensity at hp
    rw [hz] at hp
    norm_num at hp
  have hrp : completedSigmaResponse (-d) 0 ≠ 0 := by
    rw [sigma_response_conjugate d 0 hd₁ hd₂]
    exact (map_ne_zero (starRingEnd ℂ)).2 hrm
  have hFm0 : F zm ≠ 0 := by
    simpa [F, zm, completedSigmaResponse, displacedHeight] using hrm
  have hFp0 : F zp ≠ 0 := by
    simpa [F, zp, completedSigmaResponse, displacedHeight] using hrp
  constructor
  · unfold completedNativeLogResponse
    dsimp [F] at hFm hFm0
    exact hFm.deriv.neg.div (analyticAt_const.mul hFm) (mul_ne_zero (by norm_num) hFm0)
  · unfold completedNativeLogResponse
    dsimp [F] at hFp hFp0
    exact hFp.deriv.neg.div (analyticAt_const.mul hFp) (mul_ne_zero (by norm_num) hFp0)

/-- Each original sigma jet is the `(2 n + 1)`st Taylor coefficient of the real part of
the original transverse mean. This is the coefficient bridge from the log-density definition
to finite derivatives of `Q`; it uses the convergent source identities already established. -/
theorem completedSigmaLogJet_eq_transverseMeanTDerivative (d : ℝ) (n : ℕ)
    (hd₁ : -(1 / 2 : ℝ) < d) (hd₂ : d < (1 / 2 : ℝ)) :
    completedSigmaLogJet d n =
      (sigmaTransverseMeanTDerivative completedNativeLogResponse d (2 * n + 1)).re /
        ((2 * n + 1).factorial : ℝ) := by
  let L : ℝ → ℝ := fun t => Real.log (completedSigmaDensity d t)
  let Sre : ℝ → ℝ := fun t =>
    (sigmaTransverseMeanReal completedNativeLogResponse t d).re
  have hmeanComplex := completedSigmaLogJet_transverse_mean_eventually d hd₁ hd₂
  have hcast : Filter.Tendsto (fun t : ℝ => (t : ℂ)) (𝓝 0) (𝓝 0) := by
    convert Complex.continuous_ofReal.continuousAt.tendsto using 1
    simp
  have hmeanT := hcast.eventually hmeanComplex
  have hgen := completedSigmaLogJetComplexGeneratingFunction_ofReal_eq_eventually
    d hd₁ hd₂
  have hmeanRe : ∀ᶠ t : ℝ in 𝓝 0,
      Sre t = t * completedSigmaLogJetGeneratingFunction d (t ^ 2) := by
    filter_upwards [hmeanT, hgen] with t ht hg
    have ht' := ht
    rw [hg] at ht'
    have hr := congrArg Complex.re ht'
    simpa [Sre, sigmaTransverseMeanReal, Complex.mul_re] using hr
  have hlog := completedSigmaLogDensity_derivative_eq_generatingFunction_eventually
    d hd₁ hd₂
  have hderiv : (fun t : ℝ => deriv L t) =ᶠ[𝓝 0]
      (fun t : ℝ => -4 * Sre t) := by
    filter_upwards [hlog, hmeanRe] with t ht hr
    change deriv (fun x : ℝ => Real.log (completedSigmaDensity d x)) t = _ at ht
    rw [ht, hr]
    ring
  have hderivIter := Filter.EventuallyEq.iteratedDeriv_eq (2 * n + 1) hderiv
  have hcoeff := completedSigmaLogDensityDerivativeTaylorCoefficient_odd_eq_jet d n
  unfold completedSigmaLogDensityDerivativeTaylorCoefficient at hcoeff
  change iteratedDeriv (2 * n + 1) (deriv L) 0 /
      ((2 * n + 1).factorial : ℝ) = -4 * completedSigmaLogJet d n at hcoeff
  rw [hderivIter, iteratedDeriv_const_mul_field] at hcoeff
  have hjet : completedSigmaLogJet d n =
      iteratedDeriv (2 * n + 1) Sre 0 /
        ((2 * n + 1).factorial : ℝ) := by
    have hfact : ((2 * n + 1).factorial : ℝ) ≠ 0 := by positivity
    field_simp [hfact] at hcoeff
    apply (eq_div_iff hfact).2
    linarith [hcoeff]
  have hresponse := completedNativeLogResponse_analyticAt_imaginary d hd₁ hd₂
  have hmeanAnalytic := sigmaJoint_mean_analyticAt_t completedNativeLogResponse d
    hresponse.1 hresponse.2
  have hrealIter := sigmaJoint_iteratedDeriv_realPart_restrict
    (fun z : ℂ => sigmaTransverseMean completedNativeLogResponse z d) 0
    (2 * n + 1) hmeanAnalytic
  have hrealIter' : iteratedDeriv (2 * n + 1) Sre 0 =
      (sigmaTransverseMeanTDerivative completedNativeLogResponse d (2 * n + 1)).re := by
    calc
      iteratedDeriv (2 * n + 1) Sre 0 =
          (iteratedDeriv (2 * n + 1)
            (fun z : ℂ => sigmaTransverseMean completedNativeLogResponse z d) 0).re := by
              simpa [Sre, sigmaTransverseMeanReal] using hrealIter
      _ = (sigmaTransverseMeanTDerivative
          completedNativeLogResponse d (2 * n + 1)).re := by
            rw [← sigmaJoint_mean_TDerivative_eq_complex completedNativeLogResponse d
              (2 * n + 1) hresponse.1 hresponse.2]
  rw [hrealIter'] at hjet
  exact hjet

/-- The original `completedSigmaLogJet d n` is analytic in displacement throughout the
admissible strip. Its local formula is a finite derivative of the original characteristic's
logarithmic response at `± i d`. -/
theorem completedSigmaLogJet_analyticAt_displacement (d : ℝ) (n : ℕ)
    (hd₁ : -(1 / 2 : ℝ) < d) (hd₂ : d < (1 / 2 : ℝ)) :
    AnalyticAt ℝ (fun x : ℝ => completedSigmaLogJet x n) d := by
  have hresponse := completedNativeLogResponse_analyticAt_imaginary d hd₁ hd₂
  have hmean := sigmaTransverseMeanTDerivative_analyticAt completedNativeLogResponse d
    (2 * n + 1) hresponse.1 hresponse.2
  have hre : AnalyticAt ℝ
      (fun x : ℝ => (sigmaTransverseMeanTDerivative
        completedNativeLogResponse x (2 * n + 1)).re) d := by
    exact AnalyticAt.comp (f := fun x : ℝ =>
      sigmaTransverseMeanTDerivative completedNativeLogResponse x (2 * n + 1))
      (Complex.reCLM.analyticAt _).restrictScalars hmean
  have hformula : ∀ᶠ x : ℝ in 𝓝 d,
      completedSigmaLogJet x n =
        (sigmaTransverseMeanTDerivative completedNativeLogResponse x (2 * n + 1)).re /
          ((2 * n + 1).factorial : ℝ) := by
    filter_upwards [Ioo_mem_nhds hd₁ hd₂] with x hx
    exact completedSigmaLogJet_eq_transverseMeanTDerivative x n hx.1 hx.2
  have hscale : AnalyticAt ℝ (fun x : ℝ =>
      (1 / ((2 * n + 1).factorial : ℝ)) *
        (sigmaTransverseMeanTDerivative completedNativeLogResponse x (2 * n + 1)).re) d := by
    exact analyticAt_const.mul hre
  have heq : (fun x : ℝ => completedSigmaLogJet x n) =ᶠ[𝓝 d]
      (fun x : ℝ =>
        (1 / ((2 * n + 1).factorial : ℝ)) *
          (sigmaTransverseMeanTDerivative completedNativeLogResponse x (2 * n + 1)).re) := by
    filter_upwards [hformula] with x hx
    rw [hx]
    field_simp
  exact hscale.congr heq.symm

/-- A single exponential majorant works for all original sigma jets when the displacement is
small. The bound is obtained from Cauchy's estimate for the fixed source response `Q` on one
disc around the origin; it is not inferred from pointwise radii. -/
theorem completedSigmaLogJet_uniform_exponential_bound_near_center :
    ∃ ε C R : ℝ, 0 < ε ∧ 0 ≤ C ∧ 0 < R ∧
      ∀ d : ℝ, |d| < ε → ∀ n : ℕ,
        |completedSigmaLogJet d n| ≤ C * R ^ n := by
  have hFanalytic : AnalyticAt ℂ completedNativeOperatorCharacteristic 0 := by
    exact completedNativeOperatorCharacteristic_analyticAt zero_mem_completedNativeHeightDomain
  have hFne : completedNativeOperatorCharacteristic 0 ≠ 0 :=
    completedNativeOperatorCharacteristic_zero_ne_zero
  have hQanalytic : AnalyticAt ℂ completedNativeLogResponse 0 := by
    unfold completedNativeLogResponse
    exact hFanalytic.deriv.neg.div (analyticAt_const.mul hFanalytic)
      (mul_ne_zero (by norm_num) hFne)
  obtain ⟨R₀, hR₀, hQon⟩ := hQanalytic.exists_ball_analyticOnNhd
  let r : ℝ := R₀ / 4
  let ε : ℝ := min r (1 / 4)
  have hr : 0 < r := by dsimp [r]; positivity
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεr : ε ≤ r := by dsimp [ε]; exact min_le_left _ _
  have hεquarter : ε ≤ (1 / 4 : ℝ) := by dsimp [ε]; exact min_le_right _ _
  have hclosed0 : Metric.closedBall (0 : ℂ) (R₀ / 2) ⊆ Metric.ball 0 R₀ := by
    intro z hz
    have hz' : ‖z‖ ≤ R₀ / 2 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hz
    have hlt : ‖z‖ < R₀ := by linarith
    simpa [Metric.mem_ball, dist_eq_norm] using hlt
  have hcontinuous : ContinuousOn completedNativeLogResponse
      (Metric.closedBall (0 : ℂ) (R₀ / 2)) :=
    hQon.differentiableOn.continuousOn.mono hclosed0
  obtain ⟨C₀, hC₀⟩ :=
    (isCompact_closedBall (0 : ℂ) (R₀ / 2)).exists_bound_of_continuousOn hcontinuous
  let C : ℝ := max C₀ 1
  have hCpos : 0 < C := by
    dsimp [C]
    exact lt_of_lt_of_le zero_lt_one (le_max_right C₀ 1)
  have hCbound : ∀ z ∈ Metric.closedBall (0 : ℂ) (R₀ / 2),
      ‖completedNativeLogResponse z‖ ≤ C := by
    intro z hz
    exact (hC₀ z hz).trans (le_max_left C₀ 1)
  have hclosedCenter (c : ℂ) (hc : ‖c‖ ≤ r) :
      Metric.closedBall c r ⊆ Metric.closedBall (0 : ℂ) (R₀ / 2) := by
    intro z hz
    have hdist : ‖z - c‖ ≤ r := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hz
    have hnorm : ‖z‖ ≤ ‖z - c‖ + ‖c‖ := by
      calc
        ‖z‖ = ‖(z - c) + c‖ := by congr 1; abel
        _ ≤ ‖z - c‖ + ‖c‖ := norm_add_le _ _
    have hnorm' : ‖z‖ ≤ R₀ / 2 := by
      calc
        ‖z‖ ≤ ‖z - c‖ + ‖c‖ := hnorm
        _ ≤ r + r := add_le_add hdist hc
        _ = R₀ / 2 := by dsimp [r]; ring
    simpa [Metric.mem_closedBall, dist_eq_norm] using hnorm'
  have hcauchy (c : ℂ) (hc : ‖c‖ ≤ r) (k : ℕ) :
      ‖iteratedDeriv k completedNativeLogResponse c‖ ≤
        k.factorial * C / r ^ k := by
    have hcontained : Metric.closedBall c r ⊆ Metric.ball 0 R₀ :=
      (hclosedCenter c hc).trans hclosed0
    have hdiff : DiffContOnCl ℂ completedNativeLogResponse (Metric.ball c r) :=
      hQon.differentiableOn.diffContOnCl_ball hcontained
    have hCsphere : ∀ z ∈ Metric.sphere c r,
        ‖completedNativeLogResponse z‖ ≤ C := by
      intro z hz
      apply hCbound z
      exact hclosedCenter c hc (Metric.sphere_subset_closedBall hz)
    exact Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
      k hr hdiff hCsphere
  refine ⟨ε, C / r, 1 / r ^ 2, hε, by positivity, by positivity, ?_⟩
  intro d hd n
  have hd' : |d| < r := lt_of_lt_of_le hd hεr
  have hdstrip₁ : -(1 / 2 : ℝ) < d := by
    have h := (abs_lt.mp hd).1
    linarith [hεquarter]
  have hdstrip₂ : d < (1 / 2 : ℝ) := by
    have h := (abs_lt.mp hd).2
    linarith [hεquarter]
  have hnormm : ‖(0 : ℂ) - Complex.I * (d : ℂ)‖ ≤ r := by
    have heq : ‖(0 : ℂ) - Complex.I * (d : ℂ)‖ = |d| := by
      simp [Complex.norm_I]
    rw [heq]
    exact le_of_lt hd'
  have hnormp : ‖(0 : ℂ) + Complex.I * (d : ℂ)‖ ≤ r := by
    have heq : ‖(0 : ℂ) + Complex.I * (d : ℂ)‖ = |d| := by
      simp [Complex.norm_I]
    rw [heq]
    exact le_of_lt hd'
  have hresponse := completedNativeLogResponse_analyticAt_imaginary d hdstrip₁ hdstrip₂
  have hjetFormula := completedSigmaLogJet_eq_transverseMeanTDerivative d n hdstrip₁ hdstrip₂
  rw [hjetFormula, sigmaJoint_mean_t_iteratedDeriv completedNativeLogResponse d
    (2 * n + 1) hresponse.1 hresponse.2]
  let k : ℕ := 2 * n + 1
  have hCm := hcauchy ((0 : ℂ) - Complex.I * (d : ℂ)) hnormm k
  have hCp := hcauchy ((0 : ℂ) + Complex.I * (d : ℂ)) hnormp k
  have hfact : (0 : ℝ) < (k.factorial : ℝ) := by positivity
  let M : ℂ := (1 / 2 : ℂ) *
      (iteratedDeriv k completedNativeLogResponse ((0 : ℂ) - Complex.I * (d : ℂ)) +
        iteratedDeriv k completedNativeLogResponse ((0 : ℂ) + Complex.I * (d : ℂ)))
  have hnormMean : ‖M‖ ≤
      (1 / 2 : ℝ) *
        (‖iteratedDeriv k completedNativeLogResponse ((0 : ℂ) - Complex.I * (d : ℂ))‖ +
          ‖iteratedDeriv k completedNativeLogResponse ((0 : ℂ) + Complex.I * (d : ℂ))‖) := by
    dsimp [M]
    rw [norm_mul]
    have hscalar : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
    rw [hscalar]
    exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
  have hbound : |M.re / (k.factorial : ℝ)| ≤ C / r ^ k := by
    calc
      _ = |M.re| / (k.factorial : ℝ) := by rw [abs_div, abs_of_pos hfact]
      _ ≤ ‖M‖ / (k.factorial : ℝ) := by
              exact div_le_div_of_nonneg_right (Complex.abs_re_le_norm M) (le_of_lt hfact)
      _ ≤ (1 / 2 : ℝ) *
          (‖iteratedDeriv k completedNativeLogResponse ((0 : ℂ) - Complex.I * (d : ℂ))‖ +
            ‖iteratedDeriv k completedNativeLogResponse ((0 : ℂ) + Complex.I * (d : ℂ))‖) /
            (k.factorial : ℝ) := by
              exact div_le_div_of_nonneg_right hnormMean (le_of_lt hfact)
      _ ≤ (1 / 2 : ℝ) *
          ((k.factorial * C / r ^ k) + (k.factorial * C / r ^ k)) /
            (k.factorial : ℝ) := by
              apply div_le_div_of_nonneg_right
                (mul_le_mul_of_nonneg_left (add_le_add hCm hCp) (by norm_num))
                (le_of_lt hfact)
      _ = C / r ^ k := by field_simp [ne_of_gt hfact]; ring
  rw [show k = 2 * n + 1 by rfl] at hbound
  have hpow : r ^ (2 * n + 1) = r * (r ^ 2) ^ n := by
    calc
      r ^ (2 * n + 1) = r ^ (2 * n) * r := by rw [pow_add, pow_one]
      _ = (r ^ 2) ^ n * r := by rw [← pow_mul]
      _ = r * (r ^ 2) ^ n := by ring
  calc
    _ ≤ C / r ^ k := by simpa [M, k] using hbound
    _ = (C / r) * (1 / r ^ 2) ^ n := by
      rw [show k = 2 * n + 1 by rfl, hpow]
      field_simp [ne_of_gt hr]
      have hbase : r ^ 2 * (1 / r ^ 2 : ℝ) = 1 := by
        field_simp [ne_of_gt hr]
      rw [← mul_pow, hbase, one_pow]

/-- The original generating series has a common positive radius for all sufficiently small
displacements. This upgrades the pointwise radii without changing any source coefficient. -/
theorem completedSigmaLogJetGeneratingSeries_radius_uniform_near_center :
    ∃ ε ρ : ℝ, 0 < ε ∧ 0 < ρ ∧
      ∀ d : ℝ, |d| < ε →
        ENNReal.ofReal ρ ≤ (completedSigmaLogJetGeneratingSeries d).radius := by
  obtain ⟨ε, C, B, hε, hC, hB,
    hbound⟩ := completedSigmaLogJet_uniform_exponential_bound_near_center
  let ρ : ℝ := 1 / (2 * B)
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hBρ : B * ρ = (1 / 2 : ℝ) := by
    dsimp [ρ]
    field_simp [ne_of_gt hB]
  refine ⟨ε, ρ, hε, hρ, ?_⟩
  intro d hd
  let rNN : NNReal := ⟨ρ, le_of_lt hρ⟩
  have hradius : (rNN : ENNReal) ≤
      (completedSigmaLogJetGeneratingSeries d).radius := by
    apply (completedSigmaLogJetGeneratingSeries d).le_radius_of_bound C
    intro n
    change ‖FormalMultilinearSeries.ofScalars ℝ (completedSigmaLogJet d) n‖ *
        (ρ : ℝ) ^ n ≤ C
    rw [FormalMultilinearSeries.ofScalars_norm]
    have hn : ‖completedSigmaLogJet d n‖ ≤ C * B ^ n := by
      rw [Real.norm_eq_abs]
      exact hbound d hd n
    calc
      ‖completedSigmaLogJet d n‖ * ρ ^ n ≤ (C * B ^ n) * ρ ^ n :=
        mul_le_mul_of_nonneg_right hn (by positivity)
      _ = C * (B * ρ) ^ n := by rw [mul_pow]; ring
      _ = C * (1 / 2 : ℝ) ^ n := by rw [hBρ]
      _ ≤ C := by
        calc
          C * (1 / 2 : ℝ) ^ n ≤ C * 1 :=
            mul_le_mul_of_nonneg_left
              (pow_le_one₀ (by norm_num) (by norm_num : (1 / 2 : ℝ) ≤ 1)) hC
          _ = C := by ring
  have hcoe : (rNN : ENNReal) = ENNReal.ofReal ρ := by
    dsimp [rNN]
    rw [ENNReal.ofReal_eq_coe_nnreal (le_of_lt hρ)]
    congr 1
  rw [hcoe] at hradius
  exact hradius

/-- The generating-function PDE also holds at the center `u = 0`. Here its radial
term vanishes, while the value and first derivative of the convergent series are its
first two original sigma jets. The remaining equation is the `n = 0` curvature
identity, so this is a functional center statement, not only a formal coefficient claim. -/
theorem completedSigmaLogJetGeneratingFunction_transverse_pde_at_center (d : ℝ)
    (hd₁ : -(1 / 2 : ℝ) < d) (hd₂ : d < 1 / 2) :
    iteratedDeriv 2
        (fun y : ℝ => completedSigmaLogJetGeneratingFunction y 0) d +
      (6 : ℝ) * deriv
        (fun u : ℝ => completedSigmaLogJetGeneratingFunction d u) 0 +
      (4 : ℝ) * 0 ^ 2 * iteratedDeriv 2
        (fun u : ℝ => completedSigmaLogJetGeneratingFunction d u) 0 = 0 := by
  have hvalue : (fun y : ℝ => completedSigmaLogJetGeneratingFunction y 0) =
      (fun y : ℝ => completedSigmaLogJet y 0) := by
    funext y
    simp only [completedSigmaLogJetGeneratingFunction,
      completedSigmaLogJetGeneratingSeries, FormalMultilinearSeries.sum,
      FormalMultilinearSeries.ofScalars_apply_eq]
    rw [tsum_eq_single 0]
    · simp
    · intro n hn
      simp [hn]
  have hseries := completedSigmaLogJetGeneratingFunction_hasFPowerSeriesAt d hd₁ hd₂
  have hderiv : deriv (completedSigmaLogJetGeneratingFunction d) 0 =
        completedSigmaLogJet d 1 := by
    simpa [completedSigmaLogJetGeneratingSeries] using hseries.deriv
  have hcoeff := sigma_log_jet_transverse_pde_coefficient d 0 hd₁ hd₂
  rw [hvalue]
  rw [hderiv]
  simpa using hcoeff

/-- The original sigma generating function represents the transverse mean on one common
rectangle around the origin. The longitudinal radius is chosen inside a single disc of
analyticity of the original logarithmic response and inside the uniform convergence radius
proved above. -/
theorem completedSigmaLogJet_joint_representation_near_center :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ d t : ℝ, |d| < δ → |t| < δ →
        sigmaTransverseMeanReal completedNativeLogResponse t d =
          (t : ℂ) * (completedSigmaLogJetGeneratingFunction d (t ^ 2) : ℂ) := by
  obtain ⟨ε₀, ρ, hε₀, hρ, hradius⟩ :=
    completedSigmaLogJetGeneratingSeries_radius_uniform_near_center
  have hFanalytic : AnalyticAt ℂ completedNativeOperatorCharacteristic 0 :=
    completedNativeOperatorCharacteristic_analyticAt zero_mem_completedNativeHeightDomain
  have hFne : completedNativeOperatorCharacteristic 0 ≠ 0 :=
    completedNativeOperatorCharacteristic_zero_ne_zero
  have hQanalytic : AnalyticAt ℂ completedNativeLogResponse 0 := by
    unfold completedNativeLogResponse
    exact hFanalytic.deriv.neg.div (analyticAt_const.mul hFanalytic)
      (mul_ne_zero (by norm_num) hFne)
  obtain ⟨R₀, hR₀, hQon⟩ := hQanalytic.exists_ball_analyticOnNhd
  let δ : ℝ := min ε₀ (min (1 / 4) (min (R₀ / 8) (min 1 (ρ / 2))))
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hδeps : δ ≤ ε₀ := by
    dsimp [δ]
    exact min_le_left _ _
  have hδstrip : δ ≤ (1 / 4 : ℝ) := by
    dsimp [δ]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hδdisc : δ ≤ R₀ / 8 := by
    dsimp [δ]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδone : δ ≤ 1 := by
    dsimp [δ]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hδrho : δ ≤ ρ / 2 := by
    dsimp [δ]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  refine ⟨δ, hδ, ?_⟩
  intro d t hd ht
  have hdabs : |d| < δ := hd
  have htabs : |t| < δ := ht
  have hdstrip₁ : -(1 / 2 : ℝ) < d := by
    have h := (abs_lt.mp hdabs).1
    linarith [hδstrip]
  have hdstrip₂ : d < (1 / 2 : ℝ) := by
    have h := (abs_lt.mp hdabs).2
    linarith [hδstrip]
  have hqarg : |t| + |d| < R₀ := by
    have ht' : |t| < R₀ / 8 := lt_of_lt_of_le htabs hδdisc
    have hd' : |d| < R₀ / 8 := lt_of_lt_of_le hdabs hδdisc
    linarith [hR₀]
  have hminusNorm : ‖(t : ℂ) - Complex.I * (d : ℂ)‖ < R₀ := by
    calc
      ‖(t : ℂ) - Complex.I * (d : ℂ)‖ ≤ ‖(t : ℂ)‖ + ‖Complex.I * (d : ℂ)‖ := norm_sub_le _ _
      _ = |t| + |d| := by simp
      _ < R₀ := hqarg
  have hplusNorm : ‖(t : ℂ) + Complex.I * (d : ℂ)‖ < R₀ := by
    calc
      ‖(t : ℂ) + Complex.I * (d : ℂ)‖ ≤ ‖(t : ℂ)‖ + ‖Complex.I * (d : ℂ)‖ := norm_add_le _ _
      _ = |t| + |d| := by simp
      _ < R₀ := hqarg
  have hminusMem : (t : ℂ) - Complex.I * (d : ℂ) ∈ Metric.ball 0 R₀ := by
    simpa [Metric.mem_ball, dist_zero_right] using hminusNorm
  have hplusMem : (t : ℂ) + Complex.I * (d : ℂ) ∈ Metric.ball 0 R₀ := by
    simpa [Metric.mem_ball, dist_zero_right] using hplusNorm
  have hminusQ : AnalyticAt ℂ completedNativeLogResponse
      ((t : ℂ) - Complex.I * (d : ℂ)) := hQon _ hminusMem
  have hplusQ : AnalyticAt ℂ completedNativeLogResponse
      ((t : ℂ) + Complex.I * (d : ℂ)) := hQon _ hplusMem
  have hseriesRadius : ENNReal.ofReal ρ ≤
      (completedSigmaLogJetGeneratingSeries d).radius := by
    apply hradius d
    exact lt_of_lt_of_le hdabs hδeps
  have hseriesRadiusPos : 0 < (completedSigmaLogJetGeneratingSeries d).radius :=
    lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hρ) hseriesRadius
  have htabsOne : |t| < 1 := lt_of_lt_of_le htabs hδone
  have htabsRho : |t| < ρ := by
    have hhalf : ρ / 2 < ρ := by linarith
    exact lt_of_lt_of_le htabs (le_trans hδrho (le_of_lt hhalf))
  have htSqLe : |t| ^ 2 ≤ |t| := by
    calc
      |t| ^ 2 = |t| * |t| := by ring
      _ ≤ |t| * 1 := mul_le_mul_of_nonneg_left (le_of_lt htabsOne) (abs_nonneg t)
      _ = |t| := by ring
  have htSq : ‖t ^ 2‖ < ρ := by
    calc
      ‖t ^ 2‖ = |t| ^ 2 := by simp [Real.norm_eq_abs]
      _ ≤ |t| := htSqLe
      _ < ρ := htabsRho
  have htMem : (t ^ 2 : ℝ) ∈
      Metric.eball 0 (completedSigmaLogJetGeneratingSeries d).radius := by
    change edist (t ^ 2) 0 < (completedSigmaLogJetGeneratingSeries d).radius
    apply lt_of_lt_of_le _ hseriesRadius
    simpa [Metric.mem_eball, edist_dist] using
      (ENNReal.ofReal_lt_ofReal_iff hρ).mpr htSq
  have hGanalytic : AnalyticAt ℝ
      (fun u : ℝ => completedSigmaLogJetGeneratingFunction d u) (t ^ 2) := by
    unfold completedSigmaLogJetGeneratingFunction
    exact (completedSigmaLogJetGeneratingSeries d).hasFPowerSeriesOnBall
      hseriesRadiusPos |>.analyticAt_of_mem htMem
  let interval : Set ℝ := Set.Ioo (-δ) δ
  let lhs : ℝ → ℂ := fun x => sigmaTransverseMeanReal completedNativeLogResponse x d
  let rhs : ℝ → ℂ := fun x => (x : ℂ) *
    (completedSigmaLogJetGeneratingFunction d (x ^ 2) : ℂ)
  have hLanalytic : AnalyticOnNhd ℝ lhs interval := by
    intro x hx
    have hxabs : |x| < δ := abs_lt.mpr hx
    have harg : |x| + |d| < R₀ := by
      have hx' : |x| < R₀ / 8 := lt_of_lt_of_le hxabs hδdisc
      have hd' : |d| < R₀ / 8 := lt_of_lt_of_le hdabs hδdisc
      linarith [hR₀]
    have hxminusNorm : ‖(x : ℂ) - Complex.I * (d : ℂ)‖ < R₀ := by
      calc
        ‖(x : ℂ) - Complex.I * (d : ℂ)‖ ≤ ‖(x : ℂ)‖ + ‖Complex.I * (d : ℂ)‖ := norm_sub_le _ _
        _ = |x| + |d| := by simp
        _ < R₀ := harg
    have hxplusNorm : ‖(x : ℂ) + Complex.I * (d : ℂ)‖ < R₀ := by
      calc
        ‖(x : ℂ) + Complex.I * (d : ℂ)‖ ≤ ‖(x : ℂ)‖ + ‖Complex.I * (d : ℂ)‖ := norm_add_le _ _
        _ = |x| + |d| := by simp
        _ < R₀ := harg
    have hxminusMem : (x : ℂ) - Complex.I * (d : ℂ) ∈ Metric.ball 0 R₀ := by
      simpa [Metric.mem_ball, dist_zero_right] using hxminusNorm
    have hxplusMem : (x : ℂ) + Complex.I * (d : ℂ) ∈ Metric.ball 0 R₀ := by
      simpa [Metric.mem_ball, dist_zero_right] using hxplusNorm
    exact sigmaJoint_mean_analyticAt_real_t completedNativeLogResponse d x
      (hQon _ hxminusMem) (hQon _ hxplusMem)
  have hRanalytic : AnalyticOnNhd ℝ rhs interval := by
    intro x hx
    have hxabs : |x| < δ := abs_lt.mpr hx
    have hxabsOne : |x| < 1 := lt_of_lt_of_le hxabs hδone
    have hxabsRho : |x| < ρ := by
      have hhalf : ρ / 2 < ρ := by linarith
      exact lt_of_lt_of_le hxabs (le_trans hδrho (le_of_lt hhalf))
    have hxSqLe : |x| ^ 2 ≤ |x| := by
      calc
        |x| ^ 2 = |x| * |x| := by ring
        _ ≤ |x| * 1 := mul_le_mul_of_nonneg_left (le_of_lt hxabsOne) (abs_nonneg x)
        _ = |x| := by ring
    have hxSq : ‖x ^ 2‖ < ρ := by
      calc
        ‖x ^ 2‖ = |x| ^ 2 := by simp [Real.norm_eq_abs]
        _ ≤ |x| := hxSqLe
        _ < ρ := hxabsRho
    have hxMem : (x ^ 2 : ℝ) ∈
        Metric.eball 0 (completedSigmaLogJetGeneratingSeries d).radius := by
      change edist (x ^ 2) 0 < (completedSigmaLogJetGeneratingSeries d).radius
      apply lt_of_lt_of_le _ hseriesRadius
      simpa [Metric.mem_eball, edist_dist] using
        (ENNReal.ofReal_lt_ofReal_iff hρ).mpr hxSq
    have hGx : AnalyticAt ℝ
        (fun u : ℝ => completedSigmaLogJetGeneratingFunction d u) (x ^ 2) := by
      unfold completedSigmaLogJetGeneratingFunction
      exact (completedSigmaLogJetGeneratingSeries d).hasFPowerSeriesOnBall
        hseriesRadiusPos |>.analyticAt_of_mem hxMem
    have hGcast : AnalyticAt ℝ
        (fun u : ℝ => (completedSigmaLogJetGeneratingFunction d u : ℂ)) (x ^ 2) :=
      AnalyticAt.comp (f := fun u : ℝ => completedSigmaLogJetGeneratingFunction d u)
        (Complex.ofRealCLM.analyticAt
          (completedSigmaLogJetGeneratingFunction d (x ^ 2))) hGx
    have hsquare : AnalyticAt ℝ (fun y : ℝ => y ^ 2) x := by fun_prop
    have hGcomp : AnalyticAt ℝ
        (fun y : ℝ => (completedSigmaLogJetGeneratingFunction d (y ^ 2) : ℂ)) x :=
      AnalyticAt.comp (f := fun y : ℝ => y ^ 2) hGcast hsquare
    exact (Complex.ofRealCLM.analyticAt x).mul hGcomp
  have hlocal : lhs =ᶠ[𝓝 0] rhs := by
    have hcast : Filter.Tendsto (fun x : ℝ => (x : ℂ)) (𝓝 0) (𝓝 0) := by
      exact Complex.continuous_ofReal.continuousAt.tendsto
    have hmean := hcast.eventually
      (completedSigmaLogJet_transverse_mean_eventually d hdstrip₁ hdstrip₂)
    have hgen := completedSigmaLogJetComplexGeneratingFunction_ofReal_eq_eventually
      d hdstrip₁ hdstrip₂
    filter_upwards [hmean, hgen] with x hmean hgen
    dsimp [lhs, rhs, sigmaTransverseMeanReal] at hmean ⊢
    rw [hgen] at hmean
    exact hmean
  have hEqOn : Set.EqOn lhs rhs interval :=
    hLanalytic.eqOn_of_preconnected_of_eventuallyEq
      (fun x hx => hRanalytic x hx)
      (convex_Ioo (-δ) δ).isPreconnected
      (by simp [interval, hδ])
      hlocal
  have hdt : t ∈ interval := by
    exact abs_lt.mp ht
  exact hEqOn hdt

/-- The original sigma generating function satisfies the transverse radial PDE locally at
nonzero longitudinal points. All series, means, and derivatives here are the original source
objects; the common neighborhood comes from the uniform Cauchy bound above. -/
theorem completedSigmaLogJetGeneratingFunction_transverse_pde_near_center :
    ∃ η : ℝ, 0 < η ∧
      ∀ d t : ℝ, |d| < η → |t| < η → t ≠ 0 →
        iteratedDeriv 2
            (fun y : ℝ => (completedSigmaLogJetGeneratingFunction y (t ^ 2) : ℂ)) d +
          (6 : ℂ) * deriv
            (fun u : ℝ => (completedSigmaLogJetGeneratingFunction d u : ℂ)) (t ^ 2) +
          (4 : ℂ) * (t : ℂ) ^ 2 * iteratedDeriv 2
            (fun u : ℝ => (completedSigmaLogJetGeneratingFunction d u : ℂ)) (t ^ 2) = 0 := by
  obtain ⟨δrep, hδrep, hrep⟩ :=
    completedSigmaLogJet_joint_representation_near_center
  obtain ⟨ε₀, ρ, hε₀, hρ, hradius⟩ :=
    completedSigmaLogJetGeneratingSeries_radius_uniform_near_center
  have hFanalytic : AnalyticAt ℂ completedNativeOperatorCharacteristic 0 :=
    completedNativeOperatorCharacteristic_analyticAt zero_mem_completedNativeHeightDomain
  have hFne : completedNativeOperatorCharacteristic 0 ≠ 0 :=
    completedNativeOperatorCharacteristic_zero_ne_zero
  have hQanalytic : AnalyticAt ℂ completedNativeLogResponse 0 := by
    unfold completedNativeLogResponse
    exact hFanalytic.deriv.neg.div (analyticAt_const.mul hFanalytic)
      (mul_ne_zero (by norm_num) hFne)
  obtain ⟨R₀, hR₀, hQon⟩ := hQanalytic.exists_ball_analyticOnNhd
  let η : ℝ := min δrep (min ε₀ (min (1 / 4) (min (R₀ / 8) (min 1 (ρ / 2)))))
  have hη : 0 < η := by dsimp [η]; positivity
  have hηrep : η ≤ δrep := by dsimp [η]; exact min_le_left _ _
  have hηeps : η ≤ ε₀ := by
    dsimp [η]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hηstrip : η ≤ (1 / 4 : ℝ) := by
    dsimp [η]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hηdisc : η ≤ R₀ / 8 := by
    dsimp [η]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hηone : η ≤ 1 := by
    dsimp [η]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))))
  have hηrho : η ≤ ρ / 2 := by
    dsimp [η]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))))
  refine ⟨η, hη, ?_⟩
  intro d t hd ht ht0
  have hdstrip₁ : -(1 / 2 : ℝ) < d := by
    have h := (abs_lt.mp hd).1
    linarith [hηstrip]
  have hdstrip₂ : d < (1 / 2 : ℝ) := by
    have h := (abs_lt.mp hd).2
    linarith [hηstrip]
  have hseriesRadius : ENNReal.ofReal ρ ≤
      (completedSigmaLogJetGeneratingSeries d).radius := by
    apply hradius d
    exact lt_of_lt_of_le hd hηeps
  have hseriesRadiusPos : 0 < (completedSigmaLogJetGeneratingSeries d).radius :=
    lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hρ) hseriesRadius
  have htAbsOne : |t| < 1 := lt_of_lt_of_le ht hηone
  have htAbsRho : |t| < ρ := by
    have hh : ρ / 2 < ρ := by linarith
    exact lt_of_lt_of_le ht (le_trans hηrho (le_of_lt hh))
  have htSqLe : |t| ^ 2 ≤ |t| := by
    calc
      |t| ^ 2 = |t| * |t| := by ring
      _ ≤ |t| * 1 := mul_le_mul_of_nonneg_left (le_of_lt htAbsOne) (abs_nonneg t)
      _ = |t| := by ring
  have htSq : ‖t ^ 2‖ < ρ := by
    calc
      ‖t ^ 2‖ = |t| ^ 2 := by simp [Real.norm_eq_abs]
      _ ≤ |t| := htSqLe
      _ < ρ := htAbsRho
  have htMem : (t ^ 2 : ℝ) ∈
      Metric.eball 0 (completedSigmaLogJetGeneratingSeries d).radius := by
    change edist (t ^ 2) 0 < (completedSigmaLogJetGeneratingSeries d).radius
    apply lt_of_lt_of_le _ hseriesRadius
    simpa [Metric.mem_eball, edist_dist] using
      (ENNReal.ofReal_lt_ofReal_iff hρ).mpr htSq
  have hGanalytic : AnalyticAt ℝ
      (fun u : ℝ => (completedSigmaLogJetGeneratingFunction d u : ℂ)) (t ^ 2) := by
    have hGreal : AnalyticAt ℝ
        (fun u : ℝ => completedSigmaLogJetGeneratingFunction d u) (t ^ 2) := by
      unfold completedSigmaLogJetGeneratingFunction
      exact (completedSigmaLogJetGeneratingSeries d).hasFPowerSeriesOnBall
        hseriesRadiusPos |>.analyticAt_of_mem htMem
    exact AnalyticAt.comp (f := fun u : ℝ => completedSigmaLogJetGeneratingFunction d u)
      (Complex.ofRealCLM.analyticAt
        (completedSigmaLogJetGeneratingFunction d (t ^ 2))) hGreal
  have hminusNorm : ‖(t : ℂ) - Complex.I * (d : ℂ)‖ < R₀ := by
    have hsum : |t| + |d| < R₀ := by
      have ht' : |t| < R₀ / 8 := lt_of_lt_of_le ht hηdisc
      have hd' : |d| < R₀ / 8 := lt_of_lt_of_le hd hηdisc
      linarith [hR₀]
    calc
      ‖(t : ℂ) - Complex.I * (d : ℂ)‖ ≤ ‖(t : ℂ)‖ + ‖Complex.I * (d : ℂ)‖ := norm_sub_le _ _
      _ = |t| + |d| := by simp
      _ < R₀ := hsum
  have hplusNorm : ‖(t : ℂ) + Complex.I * (d : ℂ)‖ < R₀ := by
    have hsum : |t| + |d| < R₀ := by
      have ht' : |t| < R₀ / 8 := lt_of_lt_of_le ht hηdisc
      have hd' : |d| < R₀ / 8 := lt_of_lt_of_le hd hηdisc
      linarith [hR₀]
    calc
      ‖(t : ℂ) + Complex.I * (d : ℂ)‖ ≤ ‖(t : ℂ)‖ + ‖Complex.I * (d : ℂ)‖ := norm_add_le _ _
      _ = |t| + |d| := by simp
      _ < R₀ := hsum
  have hminusMem : (t : ℂ) - Complex.I * (d : ℂ) ∈ Metric.ball 0 R₀ := by
    simpa [Metric.mem_ball, dist_zero_right] using hminusNorm
  have hplusMem : (t : ℂ) + Complex.I * (d : ℂ) ∈ Metric.ball 0 R₀ := by
    simpa [Metric.mem_ball, dist_zero_right] using hplusNorm
  have hminusQ : AnalyticAt ℂ completedNativeLogResponse
      ((t : ℂ) - Complex.I * (d : ℂ)) := hQon _ hminusMem
  have hplusQ : AnalyticAt ℂ completedNativeLogResponse
      ((t : ℂ) + Complex.I * (d : ℂ)) := hQon _ hplusMem
  let S : ℝ → ℝ → ℂ := fun x y => sigmaTransverseMeanReal completedNativeLogResponse x y
  let G : ℝ → ℝ → ℂ := fun y u =>
    (completedSigmaLogJetGeneratingFunction y u : ℂ)
  have hrepresentation_t : (fun x : ℝ => S x d) =ᶠ[𝓝 t]
      (fun x : ℝ => (x : ℂ) * G d (x ^ 2)) := by
    have htmem : t ∈ Set.Ioo (-η) η := abs_lt.mp ht
    have hnhds := Ioo_mem_nhds htmem.1 htmem.2
    filter_upwards [hnhds] with x hx
    have hxabs : |x| < η := abs_lt.mpr hx
    have hxrep : |x| < δrep := lt_of_lt_of_le hxabs hηrep
    have hdrep : |d| < δrep := lt_of_lt_of_le hd hηrep
    simpa [S, G] using hrep d x hdrep hxrep
  have hrepresentation_d : (fun y : ℝ => S t y) =ᶠ[𝓝 d]
      (fun y : ℝ => (t : ℂ) * G y (t ^ 2)) := by
    have hdmem : d ∈ Set.Ioo (-η) η := abs_lt.mp hd
    have hnhds := Ioo_mem_nhds hdmem.1 hdmem.2
    filter_upwards [hnhds] with y hy
    have hyabs : |y| < η := abs_lt.mpr hy
    have hyrep : |y| < δrep := lt_of_lt_of_le hyabs hηrep
    have htrep : |t| < δrep := lt_of_lt_of_le ht hηrep
    simpa [S, G] using hrep y t hyrep htrep
  have hharmonic : iteratedDeriv 2 (fun x : ℝ => S x d) t +
      iteratedDeriv 2 (fun y : ℝ => S t y) d = 0 := by
    exact sigma_transverse_mean_harmonic completedNativeLogResponse t d hminusQ hplusQ
  simpa [S, G] using harmonic_radial_generating_pde_at_nonzero
    S G t d ht0 hrepresentation_t hrepresentation_d hharmonic hGanalytic

#print axioms completedNativeLogResponse_analyticAt_imaginary
#print axioms completedSigmaLogJet_eq_transverseMeanTDerivative
#print axioms completedSigmaLogJet_analyticAt_displacement
#print axioms completedSigmaLogJet_uniform_exponential_bound_near_center
#print axioms completedSigmaLogJetGeneratingSeries_radius_uniform_near_center
#print axioms completedSigmaLogJet_joint_representation_near_center
#print axioms completedSigmaLogJetGeneratingFunction_transverse_pde_near_center

end
end CarrySigmaObstruction
