import SigmaZeroObstruction
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Leis transversais dos jets sigma originais

Este módulo acrescenta identidades analíticas para a característica completada original.
Em particular, a segunda diferença aqui definida é apenas o stencil analítico de raio
imaginário; ela não é identificada com o bracket aritmético `C2`.
-/

namespace CarrySigmaObstruction
open CarrySelfAdjointOperator CarrySigmaSource
open CPFormal.Analytic.Cp
open Filter Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- Derivada logarítmica da característica completada original. -/
def completedNativeLogResponse (z : ℂ) : ℂ :=
  -(deriv completedNativeOperatorCharacteristic z) /
    (2 * completedNativeOperatorCharacteristic z)

/-- Média analítica transversal dos dois valores conjugadamente deslocados. -/
def sigmaTransverseMean (Q : ℂ → ℂ) (t : ℂ) (d : ℝ) : ℂ :=
  (Q (t - Complex.I * (d : ℂ)) +
    Q (t + Complex.I * (d : ℂ))) / 2

/-- Segunda diferença centrada analítica, com raio imaginário. Esta notação não designa o
bracket discreto aritmético `C2`. -/
def sigmaTransverseSecondDifference (Q : ℂ → ℂ) (t : ℂ) (d : ℝ) : ℂ :=
  Q (t - Complex.I * (d : ℂ)) - 2 * Q t +
    Q (t + Complex.I * (d : ℂ))

/-- A EDO local já estabelecida, junto à regra do produto para `D_d`, identifica a média
transversal da derivada logarítmica original com `t G_d(t²)`. Os denominadores permanecem
não nulos numa vizinhança da origem; a prova não divide por `t`, portanto inclui `t=0`. -/
theorem completedSigmaLogJet_transverse_mean_eventually (d : ℝ)
    (hd₁ : -(1 / 2 : ℝ) < d) (hd₂ : d < (1 / 2 : ℝ)) :
    ∀ᶠ z : ℂ in 𝓝 0,
      sigmaTransverseMean completedNativeLogResponse z d =
        z * completedSigmaLogJetComplexGeneratingFunction d (z ^ 2) := by
  let F : ℂ → ℂ := completedNativeOperatorCharacteristic
  let Fm : ℂ → ℂ := fun z => F (z - Complex.I * (d : ℂ))
  let Fp : ℂ → ℂ := fun z => F (z + Complex.I * (d : ℂ))
  have hdm : (0 : ℂ) - Complex.I * (d : ℂ) ∈ completedNativeHeightDomain := by
    show operatorHeightParameter ((0 : ℂ) - Complex.I * (d : ℂ)) ∈ genuineCriticalStrip
    have heq : (0 : ℂ) - Complex.I * (d : ℂ) = displacedHeight d 0 := by
      simp [displacedHeight]
    rw [heq]
    exact displacedHeight_strip d 0 hd₁ hd₂
  have hdp : (0 : ℂ) + Complex.I * (d : ℂ) ∈ completedNativeHeightDomain := by
    show operatorHeightParameter ((0 : ℂ) + Complex.I * (d : ℂ)) ∈ genuineCriticalStrip
    have heq : (0 : ℂ) + Complex.I * (d : ℂ) = displacedHeight (-d) 0 := by
      simp [displacedHeight]
    rw [heq]
    exact displacedHeight_strip (-d) 0 (by linarith) (by linarith)
  have hFm : AnalyticAt ℂ Fm 0 := by
    dsimp [Fm, F]
    exact AnalyticAt.comp (f := fun z : ℂ => z - Complex.I * (d : ℂ))
      (completedNativeOperatorCharacteristic_analyticAt hdm)
      (analyticAt_id.sub analyticAt_const)
  have hFp : AnalyticAt ℂ Fp 0 := by
    dsimp [Fp, F]
    exact AnalyticAt.comp (f := fun z : ℂ => z + Complex.I * (d : ℂ))
      (completedNativeOperatorCharacteristic_analyticAt hdp)
      (analyticAt_id.add analyticAt_const)
  have hresponse : completedSigmaResponse d 0 ≠ 0 := by
    intro hz
    have hp := completedSigmaDensity_zero_pos d hd₁ hd₂
    unfold completedSigmaDensity at hp
    rw [hz] at hp
    norm_num at hp
  have hresponsePlus : completedSigmaResponse (-d) 0 ≠ 0 := by
    rw [sigma_response_conjugate d 0 hd₁ hd₂]
    exact (map_ne_zero (starRingEnd ℂ)).2 hresponse
  have hFm0 : Fm 0 ≠ 0 := by
    simpa [Fm, F, completedSigmaResponse, displacedHeight] using hresponse
  have hFp0 : Fp 0 ≠ 0 := by
    simpa [Fp, F, completedSigmaResponse, displacedHeight] using hresponsePlus
  have hFmne : ∀ᶠ z : ℂ in 𝓝 0, Fm z ≠ 0 := hFm.continuousAt.eventually_ne hFm0
  have hFpne : ∀ᶠ z : ℂ in 𝓝 0, Fp z ≠ 0 := hFp.continuousAt.eventually_ne hFp0
  have hDne := displacedProductC_ne_zero_nhds_zero d hd₁ hd₂
  have hDiffeq := displacedProductC_local_differentialEquation d hd₁ hd₂
  filter_upwards [hFm.eventually_analyticAt, hFp.eventually_analyticAt,
    hFmne, hFpne, hDne, hDiffeq] with z hFma hFpa hFmz hFpz hDz hODE
  have hderiv : deriv (displacedProductC d) z =
      deriv F (z - Complex.I * (d : ℂ)) * F (z + Complex.I * (d : ℂ)) +
        F (z - Complex.I * (d : ℂ)) * deriv F (z + Complex.I * (d : ℂ)) := by
    change deriv (Fm * Fp) z = _
    have hderivFm : deriv Fm z = deriv F (z - Complex.I * (d : ℂ)) := by
      dsimp [Fm]
      exact deriv_comp_sub_const F (Complex.I * (d : ℂ)) z
    have hderivFp : deriv Fp z = deriv F (z + Complex.I * (d : ℂ)) := by
      dsimp [Fp]
      exact deriv_comp_add_const F (Complex.I * (d : ℂ)) z
    rw [deriv_mul hFma.differentiableAt hFpa.differentiableAt,
      hderivFm, hderivFp]
  have hquot : sigmaTransverseMean completedNativeLogResponse z d =
      -(deriv (displacedProductC d) z) /
        (4 * displacedProductC d z) := by
    unfold sigmaTransverseMean completedNativeLogResponse
    rw [hderiv]
    have hFminus : F (z - Complex.I * (d : ℂ)) ≠ 0 := by
      simpa [Fm] using hFmz
    have hFplus : F (z + Complex.I * (d : ℂ)) ≠ 0 := by
      simpa [Fp] using hFpz
    dsimp [F] at hFminus hFplus
    dsimp [displacedProductC] at hDz ⊢
    field_simp [hFminus, hFplus, hDz]
    ring
  have hODEquot : -(deriv (displacedProductC d) z) /
        (4 * displacedProductC d z) =
      z * completedSigmaLogJetComplexGeneratingFunction d (z ^ 2) := by
    have hDderiv : deriv (displacedProductC d) z =
        -4 * z * completedSigmaLogJetComplexGeneratingFunction d (z ^ 2) *
          displacedProductC d z := by
      linear_combination hODE
    rw [hDderiv]
    field_simp [hDz]
  exact hquot.trans hODEquot

/-- Decomposição puramente algébrica da média em centro e segunda diferença transversal. -/
theorem sigmaTransverseMean_eq_centeredDifference (Q : ℂ → ℂ) (t : ℂ) (d : ℝ) :
    sigmaTransverseMean Q t d =
      Q t + (1 / 2 : ℂ) * sigmaTransverseSecondDifference Q t d := by
  unfold sigmaTransverseMean sigmaTransverseSecondDifference
  ring

/-- Real-coordinate version of the transverse mean, used for its two ordinary partial
derivatives. -/
def sigmaTransverseMeanReal (Q : ℂ → ℂ) (t d : ℝ) : ℂ :=
  sigmaTransverseMean Q (t : ℂ) d

private theorem sigma_affine_path_analyticAt (Q : ℂ → ℂ) (a b : ℂ) (x : ℝ)
    (hQ : AnalyticAt ℂ Q (a + b * (x : ℂ))) :
    AnalyticAt ℝ (fun y : ℝ => Q (a + b * (y : ℂ))) x := by
  have hpath : AnalyticAt ℝ (fun y : ℝ => a + b * (y : ℂ)) x := by
    exact analyticAt_const.add (analyticAt_const.mul (Complex.ofRealCLM.analyticAt x))
  exact AnalyticAt.comp (f := fun y : ℝ => a + b * (y : ℂ))
    hQ.restrictScalars hpath

private theorem sigma_affine_path_deriv (Q : ℂ → ℂ) (a b : ℂ) (x : ℝ)
    (hQ : AnalyticAt ℂ Q (a + b * (x : ℂ))) :
    deriv (fun y : ℝ => Q (a + b * (y : ℂ))) x =
      b * deriv Q (a + b * (x : ℂ)) := by
  have hinner : HasDerivAt (fun z : ℂ => a + b * z) b (x : ℂ) := by
    simpa [mul_comm, add_comm] using
      ((hasDerivAt_id (x : ℂ)).const_mul b).const_add a
  have hpath := hinner.comp_ofReal
  calc
    deriv (fun y : ℝ => Q (a + b * (y : ℂ))) x =
        deriv Q (a + b * (x : ℂ)) *
          deriv (fun y : ℝ => a + b * (y : ℂ)) x := by
          simpa only [Function.comp_def] using
            deriv_comp_of_eq (x := x) (y := a + b * (x : ℂ))
              hQ.differentiableAt hpath.differentiableAt rfl
    _ = b * deriv Q (a + b * (x : ℂ)) := by
          rw [hpath.deriv]
          ring

/-- The first displacement derivative of the paired product `D_d(t)` vanishes at the
center for every real `t`: the two original characteristic factors contribute opposite
chain-rule terms. This is a product-symmetry cancellation, separate from the C2 bracket. -/
theorem displacedProductC_transverse_deriv_center (t : ℝ) :
    deriv (fun d : ℝ => displacedProductC d (t : ℂ)) 0 = 0 := by
  let F : ℂ → ℂ := completedNativeOperatorCharacteristic
  let fm : ℝ → ℂ := fun d => F ((t : ℂ) + (-Complex.I) * (d : ℂ))
  let fp : ℝ → ℂ := fun d => F ((t : ℂ) + Complex.I * (d : ℂ))
  have hmem : (t : ℂ) ∈ completedNativeHeightDomain := by
    change operatorHeightParameter (t : ℂ) ∈ genuineCriticalStrip
    constructor <;> norm_num [operatorHeightParameter]
  have hF : AnalyticAt ℂ F (t : ℂ) := by
    exact completedNativeOperatorCharacteristic_analyticAt hmem
  have hfmA : AnalyticAt ℝ fm 0 := by
    exact sigma_affine_path_analyticAt F (t : ℂ) (-Complex.I) 0 (by simpa using hF)
  have hfpA : AnalyticAt ℝ fp 0 := by
    exact sigma_affine_path_analyticAt F (t : ℂ) Complex.I 0 (by simpa using hF)
  have hfmD : deriv fm 0 = -Complex.I * deriv F (t : ℂ) := by
    have h := sigma_affine_path_deriv F (t : ℂ) (-Complex.I) 0 (by simpa using hF)
    simpa [fm] using h
  have hfpD : deriv fp 0 = Complex.I * deriv F (t : ℂ) := by
    have h := sigma_affine_path_deriv F (t : ℂ) Complex.I 0 (by simpa using hF)
    simpa [fp] using h
  have hproduct := (hfmA.differentiableAt.hasDerivAt).mul (hfpA.differentiableAt.hasDerivAt)
  have hzero : deriv (fun d : ℝ => fm d * fp d) 0 = 0 := by
    change deriv (fm * fp) 0 = 0
    rw [hproduct.deriv, hfmD, hfpD]
    simp [fm, fp]
    ring
  have hfun : (fun d : ℝ => fm d * fp d) =
      (fun d : ℝ => displacedProductC d (t : ℂ)) := by
    funext d
    simp only [fm, fp, F, displacedProductC, sub_eq_add_neg, neg_mul]
  simpa only [hfun] using hzero

private theorem sigma_affine_path_second_deriv (Q : ℂ → ℂ) (a b : ℂ) (x : ℝ)
    (hQ : AnalyticAt ℂ Q (a + b * (x : ℂ))) :
    iteratedDeriv 2 (fun y : ℝ => Q (a + b * (y : ℂ))) x =
      b ^ 2 * iteratedDeriv 2 Q (a + b * (x : ℂ)) := by
  let path : ℝ → ℂ := fun y => a + b * (y : ℂ)
  let f : ℝ → ℂ := fun y => Q (path y)
  have hnear : ∀ᶠ y : ℝ in 𝓝 x, AnalyticAt ℂ Q (path y) := by
    have hcont : ContinuousAt path x := by fun_prop
    exact hcont.tendsto hQ.eventually_analyticAt
  have hfirst : deriv f =ᶠ[𝓝 x] fun y : ℝ => b * deriv Q (path y) := by
    filter_upwards [hnear] with y hy
    exact sigma_affine_path_deriv Q a b y hy
  have hfirstDeriv := hfirst.deriv_eq
  have hQ' : AnalyticAt ℂ (deriv Q) (path x) := hQ.deriv
  have hsecond := sigma_affine_path_deriv (deriv Q) a b x hQ'
  calc
    iteratedDeriv 2 f x = deriv (deriv f) x := by
      simp [iteratedDeriv_succ, iteratedDeriv_zero]
    _ = deriv (fun y : ℝ => b * deriv Q (path y)) x := hfirstDeriv
    _ = b * deriv (fun y : ℝ => deriv Q (path y)) x := deriv_const_mul_field b
    _ = b * (b * deriv (deriv Q) (path x)) := by rw [hsecond]
    _ = b ^ 2 * iteratedDeriv 2 Q (path x) := by
      simp [iteratedDeriv_succ, iteratedDeriv_zero]
      ring

/-- The symmetric imaginary translate of a holomorphic function is harmonic in its two real
coordinates. The proof is the affine chain rule on the four paths; the transverse slopes square
to `-1`. -/
theorem sigma_transverse_mean_harmonic (Q : ℂ → ℂ) (t d : ℝ)
    (hminus : AnalyticAt ℂ Q ((t : ℂ) - Complex.I * (d : ℂ)))
    (hplus : AnalyticAt ℂ Q ((t : ℂ) + Complex.I * (d : ℂ))) :
    iteratedDeriv 2 (fun x : ℝ => sigmaTransverseMeanReal Q x d) t +
      iteratedDeriv 2 (fun y : ℝ => sigmaTransverseMeanReal Q t y) d = 0 := by
  let am : ℂ := -(Complex.I * (d : ℂ))
  let ap : ℂ := Complex.I * (d : ℂ)
  let qmT : ℝ → ℂ := fun x => Q (am + 1 * (x : ℂ))
  let qpT : ℝ → ℂ := fun x => Q (ap + 1 * (x : ℂ))
  let qmD : ℝ → ℂ := fun y => Q ((t : ℂ) + (-Complex.I) * (y : ℂ))
  let qpD : ℝ → ℂ := fun y => Q ((t : ℂ) + Complex.I * (y : ℂ))
  have hminusPathT : AnalyticAt ℂ Q (am + 1 * (t : ℂ)) := by
    dsimp [am]
    convert hminus using 1
    ring
  have hplusPathT : AnalyticAt ℂ Q (ap + 1 * (t : ℂ)) := by
    dsimp [ap]
    convert hplus using 1
    ring
  have hminusPathD : AnalyticAt ℂ Q ((t : ℂ) + (-Complex.I) * (d : ℂ)) := by
    convert hminus using 1
    ring
  have hplusPathD : AnalyticAt ℂ Q ((t : ℂ) + Complex.I * (d : ℂ)) := by
    exact hplus
  have hminusT : AnalyticAt ℝ qmT t := by
    exact sigma_affine_path_analyticAt Q am 1 t hminusPathT
  have hplusT : AnalyticAt ℝ qpT t := by
    exact sigma_affine_path_analyticAt Q ap 1 t hplusPathT
  have hminusD : AnalyticAt ℝ qmD d := by
    exact sigma_affine_path_analyticAt Q (t : ℂ) (-Complex.I) d hminusPathD
  have hplusD : AnalyticAt ℝ qpD d := by
    exact sigma_affine_path_analyticAt Q (t : ℂ) Complex.I d hplusPathD
  have hminusT₂ : iteratedDeriv 2 qmT t = iteratedDeriv 2 Q
      ((t : ℂ) - Complex.I * (d : ℂ)) := by
    have h := sigma_affine_path_second_deriv Q am 1 t hminusPathT
    calc
      iteratedDeriv 2 qmT t =
          iteratedDeriv 2 (fun x : ℝ => Q (am + 1 * (x : ℂ))) t := by rfl
      _ = iteratedDeriv 2 Q (am + 1 * (t : ℂ)) := by simpa using h
      _ = iteratedDeriv 2 Q ((t : ℂ) - Complex.I * (d : ℂ)) := by
          congr 1
          dsimp [am]
          ring
  have hplusT₂ : iteratedDeriv 2 qpT t = iteratedDeriv 2 Q
      ((t : ℂ) + Complex.I * (d : ℂ)) := by
    have h := sigma_affine_path_second_deriv Q ap 1 t hplusPathT
    calc
      iteratedDeriv 2 qpT t =
          iteratedDeriv 2 (fun x : ℝ => Q (ap + 1 * (x : ℂ))) t := by rfl
      _ = iteratedDeriv 2 Q (ap + 1 * (t : ℂ)) := by simpa using h
      _ = iteratedDeriv 2 Q ((t : ℂ) + Complex.I * (d : ℂ)) := by
          congr 1
          dsimp [ap]
          ring
  have hminusD₂ : iteratedDeriv 2 qmD d = -iteratedDeriv 2 Q
      ((t : ℂ) - Complex.I * (d : ℂ)) := by
    have h := sigma_affine_path_second_deriv Q (t : ℂ) (-Complex.I) d hminusPathD
    calc
      iteratedDeriv 2 qmD d =
          iteratedDeriv 2 (fun y : ℝ => Q ((t : ℂ) + (-Complex.I) * (y : ℂ))) d := by rfl
      _ = (-Complex.I) ^ 2 * iteratedDeriv 2 Q
          ((t : ℂ) + (-Complex.I) * (d : ℂ)) := h
      _ = -iteratedDeriv 2 Q ((t : ℂ) - Complex.I * (d : ℂ)) := by
          have hni : (-Complex.I) ^ 2 = -1 := by
            rw [pow_two, neg_mul_neg, Complex.I_mul_I]
          rw [hni]
          simp [sub_eq_add_neg]
  have hplusD₂ : iteratedDeriv 2 qpD d = -iteratedDeriv 2 Q
      ((t : ℂ) + Complex.I * (d : ℂ)) := by
    have h := sigma_affine_path_second_deriv Q (t : ℂ) Complex.I d hplusPathD
    calc
      iteratedDeriv 2 qpD d =
          iteratedDeriv 2 (fun y : ℝ => Q ((t : ℂ) + Complex.I * (y : ℂ))) d := by rfl
      _ = Complex.I ^ 2 * iteratedDeriv 2 Q
          ((t : ℂ) + Complex.I * (d : ℂ)) := h
      _ = -iteratedDeriv 2 Q ((t : ℂ) + Complex.I * (d : ℂ)) := by
          have hi : Complex.I ^ 2 = -1 := by rw [pow_two, Complex.I_mul_I]
          rw [hi]
          ring
  have hmeanT : (fun x : ℝ => sigmaTransverseMeanReal Q x d) =
      (fun x => (1 / 2 : ℂ) * (qmT x + qpT x)) := by
    funext x
    simp [sigmaTransverseMeanReal, sigmaTransverseMean, qmT, qpT, am, ap]
    ring
  have hmeanD : (fun y : ℝ => sigmaTransverseMeanReal Q t y) =
      (fun y => (1 / 2 : ℂ) * (qmD y + qpD y)) := by
    funext y
    simp [sigmaTransverseMeanReal, sigmaTransverseMean, qmD, qpD]
    ring
  rw [hmeanT, hmeanD]
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field]
  have hsumT : iteratedDeriv 2 (fun x : ℝ => qmT x + qpT x) t =
      iteratedDeriv 2 qmT t + iteratedDeriv 2 qpT t := by
    exact iteratedDeriv_add (n := 2) (f := qmT) (g := qpT) (x := t)
      hminusT.contDiffAt hplusT.contDiffAt
  have hsumD : iteratedDeriv 2 (fun y : ℝ => qmD y + qpD y) d =
      iteratedDeriv 2 qmD d + iteratedDeriv 2 qpD d := by
    exact iteratedDeriv_add (n := 2) (f := qmD) (g := qpD) (x := d)
      hminusD.contDiffAt hplusD.contDiffAt
  rw [hsumT, hsumD]
  rw [hminusT₂, hplusT₂, hminusD₂, hplusD₂]
  ring

/-- Forma da identidade de partida em termos do stencil transversal analítico. -/
theorem completedSigmaLogJet_centeredDifference_eventually (d : ℝ)
    (hd₁ : -(1 / 2 : ℝ) < d) (hd₂ : d < (1 / 2 : ℝ)) :
    ∀ᶠ z : ℂ in 𝓝 0,
      z * completedSigmaLogJetComplexGeneratingFunction d (z ^ 2) =
        completedNativeLogResponse z +
          (1 / 2 : ℂ) * sigmaTransverseSecondDifference
            completedNativeLogResponse z d := by
  filter_upwards [completedSigmaLogJet_transverse_mean_eventually d hd₁ hd₂]
    with z hz
  calc
    z * completedSigmaLogJetComplexGeneratingFunction d (z ^ 2) =
        sigmaTransverseMean completedNativeLogResponse z d := hz.symm
    _ = completedNativeLogResponse z +
        (1 / 2 : ℂ) * sigmaTransverseSecondDifference completedNativeLogResponse z d :=
      sigmaTransverseMean_eq_centeredDifference _ _ _

private theorem iteratedDeriv_add_right (m n : ℕ) (f : ℝ → ℝ) :
    iteratedDeriv (m + n) f = iteratedDeriv m (iteratedDeriv n f) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Nat.succ_add, iteratedDeriv_succ, iteratedDeriv_succ, ih]

private theorem sigma_log_jet_curvature_eventually (d : ℝ) (n : ℕ)
    (hd₁ : -(1 / 2 : ℝ) < d) (hd₂ : d < (1 / 2 : ℝ)) :
    (fun x : ℝ => iteratedDeriv 2 (fun y => completedSigmaLogJet y n) x) =ᶠ[𝓝 d]
      (fun x : ℝ => -2 * ((n : ℝ) + 1) * (2 * (n : ℝ) + 3) *
        completedSigmaLogJet x (n + 1)) := by
  filter_upwards [Ioo_mem_nhds hd₁ hd₂] with x hx
  have ha : AnalyticAt ℂ completedNativeOperatorCharacteristic (displacedHeight x 0) :=
    completedNativeOperatorCharacteristic_analyticAt
      (displacedHeight_strip x 0 hx.1 hx.2)
  have hne : completedSigmaResponse x 0 ≠ 0 := by
    intro hzero
    have hp := completedSigmaDensity_zero_pos x hx.1 hx.2
    unfold completedSigmaDensity at hp
    rw [hzero] at hp
    norm_num at hp
  exact sigma_log_jet_curvature_at x n ha hne

private theorem sigma_log_jet_all_order_coefficient_step (n m : ℕ) :
    -2 * ((n : ℝ) + 1) * (2 * (n : ℝ) + 3) *
        ((-1 : ℝ) ^ m *
          (((2 * n + 2 * m + 3).factorial : ℝ) /
            ((2 * n + 3).factorial : ℝ))) =
      (-1 : ℝ) ^ (m + 1) *
        (((2 * n + 2 * m + 3).factorial : ℝ) /
          ((2 * n + 1).factorial : ℝ)) := by
  have hfact : ((2 * n + 3).factorial : ℝ) =
      (2 * (n : ℝ) + 3) * (2 * (n : ℝ) + 2) *
        ((2 * n + 1).factorial : ℝ) := by
    have h₁ : 2 * n + 3 = (2 * n + 2) + 1 := by omega
    have h₂ : 2 * n + 2 = (2 * n + 1) + 1 := by omega
    rw [h₁, Nat.factorial_succ, h₂, Nat.factorial_succ]
    push_cast
    ring
  have hden₁ : ((2 * n + 3).factorial : ℝ) ≠ 0 := by positivity
  have hden₂ : ((2 * n + 1).factorial : ℝ) ≠ 0 := by positivity
  rw [pow_succ, hfact]
  field_simp [hden₁, hden₂]

/-- The all-order even transverse law for the original sigma jets. The curvature identity
is applied pointwise on the admissible strip, then differentiated as a local identity. -/
theorem sigma_log_jet_even_deriv_all_order (d : ℝ) (n m : ℕ)
    (hd₁ : -(1 / 2 : ℝ) < d) (hd₂ : d < (1 / 2 : ℝ)) :
    iteratedDeriv (2 * m) (fun x : ℝ => completedSigmaLogJet x n) d =
      (-1 : ℝ) ^ m *
        (((2 * n + 2 * m + 1).factorial : ℝ) /
          ((2 * n + 1).factorial : ℝ)) *
        completedSigmaLogJet d (n + m) := by
  induction m generalizing d n hd₁ hd₂ with
  | zero =>
      simp only [Nat.mul_zero, Nat.add_zero, iteratedDeriv_zero, pow_zero]
      have hfact : ((2 * n + 1).factorial : ℝ) ≠ 0 := by positivity
      rw [div_self hfact, one_mul]
      simp
  | succ m ih =>
      have hcurv := Filter.EventuallyEq.iteratedDeriv_eq (2 * m)
        (sigma_log_jet_curvature_eventually d n hd₁ hd₂)
      have hstep : iteratedDeriv (2 * (m + 1))
          (fun x : ℝ => completedSigmaLogJet x n) d =
          -2 * ((n : ℝ) + 1) * (2 * (n : ℝ) + 3) *
            iteratedDeriv (2 * m)
              (fun x : ℝ => completedSigmaLogJet x (n + 1)) d := by
        have hindex : 2 * (m + 1) = 2 * m + 2 := by omega
        rw [hindex]
        have hcompose := congrFun
          (iteratedDeriv_add_right (2 * m) 2
            (fun x : ℝ => completedSigmaLogJet x n)) d
        rw [hcompose, hcurv, iteratedDeriv_const_mul_field]
      calc
        iteratedDeriv (2 * (m + 1))
            (fun x : ℝ => completedSigmaLogJet x n) d =
            -2 * ((n : ℝ) + 1) * (2 * (n : ℝ) + 3) *
              iteratedDeriv (2 * m)
                (fun x : ℝ => completedSigmaLogJet x (n + 1)) d := hstep
        _ = -2 * ((n : ℝ) + 1) * (2 * (n : ℝ) + 3) *
              (((-1 : ℝ) ^ m *
                (((2 * (n + 1) + 2 * m + 1).factorial : ℝ) /
                  ((2 * (n + 1) + 1).factorial : ℝ))) *
                completedSigmaLogJet d (n + 1 + m)) := by
              rw [ih d (n + 1) hd₁ hd₂]
        _ = (-1 : ℝ) ^ (m + 1) *
              (((2 * n + 2 * (m + 1) + 1).factorial : ℝ) /
                ((2 * n + 1).factorial : ℝ)) *
              completedSigmaLogJet d (n + (m + 1)) := by
              have hidx₁ : 2 * (n + 1) + 2 * m + 1 = 2 * n + 2 * m + 3 := by omega
              have hidx₂ : 2 * (n + 1) + 1 = 2 * n + 3 := by omega
              have hidx₃ : 2 * n + 2 * (m + 1) + 1 = 2 * n + 2 * m + 3 := by omega
              rw [hidx₁, hidx₂, hidx₃]
              rw [show n + 1 + m = n + (m + 1) by omega]
              calc
                _ = (-2 * ((n : ℝ) + 1) * (2 * (n : ℝ) + 3) *
                    ((-1 : ℝ) ^ m *
                      (((2 * n + 2 * m + 3).factorial : ℝ) /
                        ((2 * n + 3).factorial : ℝ)))) *
                    completedSigmaLogJet d (n + (m + 1)) := by ring
                _ = ((-1 : ℝ) ^ (m + 1) *
                    (((2 * n + 2 * m + 3).factorial : ℝ) /
                      ((2 * n + 1).factorial : ℝ))) *
                    completedSigmaLogJet d (n + (m + 1)) := by
                    rw [sigma_log_jet_all_order_coefficient_step]
                _ = _ := by ring

/-- Coefficientwise form of the transverse PDE. The coefficient of `u^n` in
`4u ∂ᵤ² G + 6 ∂ᵤ G` is `2(n+1)(2n+3)h_(n+1)`, which cancels the second displacement
derivative of `h_n`. This is a formal coefficient identity; it does not by itself assert
termwise differentiability of the full generating sum in `d`. -/
theorem sigma_log_jet_transverse_pde_coefficient (d : ℝ) (n : ℕ)
    (hd₁ : -(1 / 2 : ℝ) < d) (hd₂ : d < (1 / 2 : ℝ)) :
    iteratedDeriv 2 (fun x : ℝ => completedSigmaLogJet x n) d +
      (4 * (n : ℝ) * ((n : ℝ) + 1) + 6 * ((n : ℝ) + 1)) *
        completedSigmaLogJet d (n + 1) = 0 := by
  have ha : AnalyticAt ℂ completedNativeOperatorCharacteristic (displacedHeight d 0) :=
    completedNativeOperatorCharacteristic_analyticAt (displacedHeight_strip d 0 hd₁ hd₂)
  have hne : completedSigmaResponse d 0 ≠ 0 := by
    intro hzero
    have hp := completedSigmaDensity_zero_pos d hd₁ hd₂
    unfold completedSigmaDensity at hp
    rw [hzero] at hp
    norm_num at hp
  rw [sigma_log_jet_curvature_at d n ha hne]
  ring

/-- Every odd iterated derivative of an original sigma jet vanishes at the center.
Analyticity of the original jet at zero supplies derivatives of every finite order;
the equality itself follows by differentiating the local parity identity. -/
theorem sigma_log_jet_odd_deriv_center (n m : ℕ) :
    iteratedDeriv (2 * m + 1) (fun d : ℝ => completedSigmaLogJet d n) 0 = 0 := by
  have hanalytic := sigma_log_jet_analytic_center n
  let g : ℝ → ℝ := fun d => completedSigmaLogJet d n
  have _hregular : ContDiffAt ℝ (2 * m + 1)
      g 0 :=
    hanalytic.contDiffAt.of_le le_top
  have heven : (fun d : ℝ => g (-d)) =ᶠ[𝓝 0]
      (fun d : ℝ => g d) := by
    filter_upwards [Ioo_mem_nhds (by norm_num : -(1 / 2 : ℝ) < 0)
      (by norm_num : (0 : ℝ) < 1 / 2)] with d hd
    exact sigma_log_jet_even d hd.1 hd.2 n
  have hderiv := Filter.EventuallyEq.iteratedDeriv_eq (2 * m + 1) heven
  rw [iteratedDeriv_comp_neg] at hderiv
  have hpow : (-1 : ℝ) ^ (2 * m + 1) = -1 := by
    rw [show 2 * m + 1 = m * 2 + 1 by omega, pow_add]
    simp
  simp only [hpow, smul_eq_mul, neg_zero] at hderiv
  linarith

/-- Coeficiente de `d^(2m)` na série transversal local do jet original `h_n`. -/
def sigmaLogJetTransverseTaylorCoefficient (n m : ℕ) : ℝ :=
  (-1 : ℝ) ^ m * (Nat.choose (2 * n + 2 * m + 1) (2 * m) : ℝ) *
    completedSigmaLogJet 0 (n + m)

private theorem sigmaLogJet_choose_factorial_ratio (n m : ℕ) :
    (Nat.choose (2 * n + 2 * m + 1) (2 * m) : ℝ) =
      (((2 * n + 2 * m + 1).factorial : ℝ) /
        ((2 * n + 1).factorial : ℝ)) /
        ((2 * m).factorial : ℝ) := by
  have hle : 2 * m ≤ 2 * n + 2 * m + 1 := by omega
  have hnat : Nat.choose (2 * n + 2 * m + 1) (2 * m) *
      (2 * m).factorial * (2 * n + 2 * m + 1 - 2 * m).factorial =
        (2 * n + 2 * m + 1).factorial :=
    Nat.choose_mul_factorial_mul_factorial hle
  have hnat' : Nat.choose (2 * n + 2 * m + 1) (2 * m) *
      (2 * m).factorial * (2 * n + 1).factorial =
        (2 * n + 2 * m + 1).factorial := by
    simpa [show 2 * n + 2 * m + 1 - 2 * m = 2 * n + 1 by omega] using hnat
  have hreal : (Nat.choose (2 * n + 2 * m + 1) (2 * m) : ℝ) *
      ((2 * m).factorial : ℝ) * ((2 * n + 1).factorial : ℝ) =
        ((2 * n + 2 * m + 1).factorial : ℝ) := by
    exact_mod_cast hnat'
  have h₁ : ((2 * m).factorial : ℝ) ≠ 0 := by positivity
  have h₂ : ((2 * n + 1).factorial : ℝ) ≠ 0 := by positivity
  field_simp [h₁, h₂]
  nlinarith [hreal]

/-- The Taylor coefficient is the all-order derivative divided by `(2m)!`. -/
theorem sigma_log_jet_even_taylor_coefficient (n m : ℕ) :
    iteratedDeriv (2 * m) (fun d : ℝ => completedSigmaLogJet d n) 0 /
        ((2 * m).factorial : ℝ) =
      sigmaLogJetTransverseTaylorCoefficient n m := by
  rw [sigma_log_jet_even_deriv_all_order 0 n m (by norm_num) (by norm_num)]
  rw [sigmaLogJetTransverseTaylorCoefficient,
    sigmaLogJet_choose_factorial_ratio]
  have hfact : ((2 * m).factorial : ℝ) ≠ 0 := by positivity
  field_simp [hfact]

/-- Odd Taylor coefficients of the original transverse jet vanish. -/
theorem sigma_log_jet_odd_taylor_coefficient (n m : ℕ) :
    iteratedDeriv (2 * m + 1) (fun d : ℝ => completedSigmaLogJet d n) 0 /
        ((2 * m + 1).factorial : ℝ) = 0 := by
  rw [sigma_log_jet_odd_deriv_center n m]
  simp

/-- The full coefficient sequence with the proven even coefficients and zero odd
coefficients. -/
def sigmaLogJetTransverseTaylorCoefficientAll (n k : ℕ) : ℝ :=
  if k % 2 = 0 then sigmaLogJetTransverseTaylorCoefficient n (k / 2) else 0

/-- Power series of the original transverse jet, with its explicit parity-separated
coefficients. -/
def sigmaLogJetTransverseTaylorSeries (n : ℕ) :
    FormalMultilinearSeries ℝ ℝ ℝ :=
  FormalMultilinearSeries.ofScalars ℝ (sigmaLogJetTransverseTaylorCoefficientAll n)

private theorem sigmaLogJetTaylorCoefficientAll_eq_derivative (n k : ℕ) :
    sigmaLogJetTransverseTaylorCoefficientAll n k =
      iteratedDeriv k (fun d : ℝ => completedSigmaLogJet d n) 0 /
        (k.factorial : ℝ) := by
  by_cases heven : k % 2 = 0
  · have hk : k = 2 * (k / 2) := by omega
    rw [sigmaLogJetTransverseTaylorCoefficientAll, if_pos heven, hk]
    have hdiv : 2 * (k / 2) / 2 = k / 2 := by omega
    rw [hdiv]
    exact (sigma_log_jet_even_taylor_coefficient n (k / 2)).symm
  · have hodd : k % 2 = 1 := by
      have hm := Nat.mod_lt k (by norm_num : 0 < 2)
      omega
    have hk : k = 2 * (k / 2) + 1 := by omega
    rw [sigmaLogJetTransverseTaylorCoefficientAll, if_neg heven, hk]
    exact (sigma_log_jet_odd_taylor_coefficient n (k / 2)).symm

/-- The explicit transverse coefficient series is the genuine Taylor series of the
original analytic jet at zero, so it converges to the jet on a neighborhood. -/
theorem sigma_log_jet_transverse_hasFPowerSeriesAt (n : ℕ) :
    HasFPowerSeriesAt (fun d : ℝ => completedSigmaLogJet d n)
      (sigmaLogJetTransverseTaylorSeries n) 0 := by
  have hanalytic := sigma_log_jet_analytic_center n
  have hTaylor := hanalytic.hasFPowerSeriesAt
  have hseries : sigmaLogJetTransverseTaylorSeries n =
      FormalMultilinearSeries.ofScalars ℝ
        (fun k => iteratedDeriv k (fun d : ℝ => completedSigmaLogJet d n) 0 /
          (k.factorial : ℝ)) := by
    ext k
    simp [sigmaLogJetTransverseTaylorSeries, sigmaLogJetTaylorCoefficientAll_eq_derivative]
  rw [hseries]
  exact hTaylor

private def evenIndexEquiv : ℕ ≃ {k : ℕ // k % 2 = 0} where
  toFun n := ⟨2 * n, by omega⟩
  invFun k := k.1 / 2
  left_inv n := by simp
  right_inv k := by
    rcases k with ⟨k, hk⟩
    apply Subtype.ext
    change 2 * (k / 2) = k
    have hmod := Nat.mod_add_div k 2
    rw [hk] at hmod
    omega

/-- The transverse Taylor expansion is an actual convergent sum of the displayed even
coefficients on some neighborhood of zero. This is local analyticity, with no global-radius
claim. -/
theorem sigma_log_jet_transverse_tsum_eventually (n : ℕ) :
    ∀ᶠ d : ℝ in 𝓝 0,
      Summable (fun m : ℕ =>
        sigmaLogJetTransverseTaylorCoefficient n m * d ^ (2 * m)) ∧
      completedSigmaLogJet d n = ∑' m : ℕ,
        sigmaLogJetTransverseTaylorCoefficient n m * d ^ (2 * m) := by
  let O : Set ℕ := {k | k % 2 = 0}
  have hseries := sigma_log_jet_transverse_hasFPowerSeriesAt n
  have hsumEventually := hseries.eventually_hasSum_sub
  filter_upwards [hsumEventually] with d hsum
  have hsum' : HasSum
      (fun k : ℕ => sigmaLogJetTransverseTaylorCoefficientAll n k * d ^ k)
      (completedSigmaLogJet d n) := by
    simpa [sigmaLogJetTransverseTaylorSeries,
      FormalMultilinearSeries.ofScalars_apply_eq, mul_comm] using hsum
  let f : ℕ → ℝ := fun k => sigmaLogJetTransverseTaylorCoefficientAll n k * d ^ k
  have hdecomp := hsum'.summable.tsum_subtype_add_tsum_subtype_compl O
  have hcomplement : ∑' k : (Oᶜ : Set ℕ), f k.val = 0 := by
    have hall : ∀ k : (Oᶜ : Set ℕ), f k.val = 0 := by
      intro k
      have hkO : k.val % 2 ≠ 0 := by
        intro hk
        exact k.property hk
      simp [f, sigmaLogJetTransverseTaylorCoefficientAll, hkO]
    simp [hall]
  have htotalEven : completedSigmaLogJet d n = ∑' k : (O : Set ℕ), f k.val := by
    calc
      completedSigmaLogJet d n = ∑' k : ℕ, f k := hsum'.tsum_eq.symm
      _ = (∑' k : (O : Set ℕ), f k.val) + ∑' k : (Oᶜ : Set ℕ), f k.val := by
        simpa [f] using hdecomp.symm
      _ = ∑' k : (O : Set ℕ), f k.val := by rw [hcomplement, add_zero]
  have hreindex : (∑' k : (O : Set ℕ), f k.val) = ∑' m : ℕ, f (2 * m) := by
    calc
      (∑' k : (O : Set ℕ), f k.val) =
          ∑' k : {k : ℕ // k % 2 = 0}, f k.val := rfl
      _ = ∑' m : ℕ, f (2 * m) :=
        (Equiv.tsum_eq evenIndexEquiv (fun k : {k : ℕ // k % 2 = 0} => f k.val)).symm
  have hterms : (∑' m : ℕ, f (2 * m)) = ∑' m : ℕ,
      sigmaLogJetTransverseTaylorCoefficient n m * d ^ (2 * m) := by
    apply tsum_congr
    intro m
    simp [f, sigmaLogJetTransverseTaylorCoefficientAll]
  have hsubtypeSummable : Summable (fun k : (O : Set ℕ) => f k.val) :=
    hsum'.summable.subtype O
  have hmSummable : Summable (fun m : ℕ => f (2 * m)) := by
    simpa [Function.comp_def, evenIndexEquiv] using
      hsubtypeSummable.comp_injective evenIndexEquiv.injective
  have hmSummable' : Summable (fun m : ℕ =>
      sigmaLogJetTransverseTaylorCoefficient n m * d ^ (2 * m)) := by
    apply hmSummable.congr
    intro m
    simp [f, sigmaLogJetTransverseTaylorCoefficientAll]
  exact ⟨hmSummable', htotalEven.trans (hreindex.trans hterms)⟩

/-- All displayed normalizations for the first six nonconstant coefficients follow
symbolically from the exact binomial formula. -/
theorem sigma_log_jet_transverse_coefficients_n0 (h : ℕ → ℝ) :
    (-1 : ℝ) ^ 1 * (Nat.choose (3 : ℕ) 2 : ℝ) * h 1 = -3 * h 1 ∧
    (-1 : ℝ) ^ 2 * (Nat.choose (5 : ℕ) 4 : ℝ) * h 2 = 5 * h 2 ∧
    (-1 : ℝ) ^ 3 * (Nat.choose (7 : ℕ) 6 : ℝ) * h 3 = -7 * h 3 := by
  norm_num [Nat.choose]

theorem sigma_log_jet_transverse_coefficients_n1 (h : ℕ → ℝ) :
    (-1 : ℝ) ^ 1 * (Nat.choose (5 : ℕ) 2 : ℝ) * h 2 = -10 * h 2 ∧
    (-1 : ℝ) ^ 2 * (Nat.choose (7 : ℕ) 4 : ℝ) * h 3 = 35 * h 3 ∧
    (-1 : ℝ) ^ 3 * (Nat.choose (9 : ℕ) 6 : ℝ) * h 4 = -84 * h 4 := by
  norm_num [Nat.choose]

/-- The prescribed second- and fourth-derivative normalization checks. -/
theorem sigma_log_jet_second_and_fourth_deriv_check (n : ℕ) :
    iteratedDeriv 2 (fun d : ℝ => completedSigmaLogJet d n) 0 =
        -2 * ((n : ℝ) + 1) * (2 * (n : ℝ) + 3) * completedSigmaLogJet 0 (n + 1) ∧
    iteratedDeriv 4 (fun d : ℝ => completedSigmaLogJet d n) 0 =
        (((2 * n + 5).factorial : ℝ) /
          ((2 * n + 1).factorial : ℝ)) * completedSigmaLogJet 0 (n + 2) := by
  constructor
  · have h := sigma_log_jet_curvature_center n
    rw [← sigma_log_jet_center_eq_canonical] at h
    exact h
  · simpa using sigma_log_jet_even_deriv_all_order 0 n 2 (by norm_num) (by norm_num)

#print axioms completedSigmaLogJet_transverse_mean_eventually
#print axioms completedSigmaLogJet_centeredDifference_eventually
#print axioms sigma_transverse_mean_harmonic
#print axioms sigma_log_jet_even_deriv_all_order
#print axioms sigma_log_jet_odd_deriv_center
#print axioms sigma_log_jet_transverse_hasFPowerSeriesAt
#print axioms sigma_log_jet_transverse_tsum_eventually
#print axioms sigma_log_jet_transverse_pde_coefficient
#print axioms displacedProductC_transverse_deriv_center

end
end CarrySigmaObstruction
