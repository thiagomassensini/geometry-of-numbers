import CarrySelfAdjointOperator.CompletedNativeThetaCubicQuadrature
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! Scalar derivatives of each mode of the original, unchanged theta source.
No differentiability of a Hilbert-valued state is assumed. -/
namespace CarryIntegralCertificate
open CarrySelfAdjointOperator Real Set Filter MeasureTheory Polynomial
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

/-- Twice a mode, matching the normalization of `thetaTail`. -/
def thetaMode (m : ℕ) (u : ℝ) : ℝ := 2*XiThetaCosine.thetaTailMode m u

def thetaArgument (m : ℕ) (u : ℝ) : ℝ :=
  Real.pi*((m+1:ℕ):ℝ)^2*exp (2*u)

/-- The rational polynomial multiplying the nth scalar derivative. -/
def thetaDerivativePolynomial : ℕ → Polynomial ℚ
  | 0 => 1
  | n+1 => (C (1/2)-C 2*X)*thetaDerivativePolynomial n +
      C 2*X*(thetaDerivativePolynomial n).derivative

def thetaModeDerivative (m n : ℕ) (u : ℝ) : ℝ :=
  aeval (thetaArgument m u) (thetaDerivativePolynomial n)*thetaMode m u

theorem hasDerivAt_thetaArgument (m : ℕ) (u : ℝ) :
    HasDerivAt (thetaArgument m) (2*thetaArgument m u) u := by
  have h := (((hasDerivAt_id u).const_mul 2).exp.const_mul
    (Real.pi*((m+1:ℕ):ℝ)^2))
  exact h.congr_deriv (by dsimp [thetaArgument]; ring)

theorem hasDerivAt_thetaMode (m : ℕ) (u : ℝ) :
    HasDerivAt (thetaMode m) ((1/2-2*thetaArgument m u)*thetaMode m u) u := by
  have h1 := ((hasDerivAt_id u).div_const 2).exp
  have h2 := ((hasDerivAt_thetaArgument m u).neg).exp
  refine ((h1.mul h2).const_mul 2).congr_of_eventuallyEq
    (Eventually.of_forall (fun x => ?_)) |>.congr_deriv ?_
  · dsimp [thetaMode,XiThetaCosine.thetaTailMode,thetaArgument]
    congr 2; ring
  · dsimp [thetaMode,XiThetaCosine.thetaTailMode,thetaArgument]
    ring

theorem hasDerivAt_thetaModeDerivative (m n : ℕ) (u : ℝ) :
    HasDerivAt (thetaModeDerivative m n) (thetaModeDerivative m (n+1) u) u := by
  have hp := ((thetaDerivativePolynomial n).hasDerivAt_aeval
    (thetaArgument m u)).comp u (hasDerivAt_thetaArgument m u)
  refine (hp.mul (hasDerivAt_thetaMode m u)).congr_of_eventuallyEq
    (Eventually.of_forall (fun _ => rfl)) |>.congr_deriv ?_
  dsimp [thetaModeDerivative,thetaDerivativePolynomial]
  simp only [map_add,map_mul,map_sub,aeval_C,aeval_X]
  simp only [map_div₀,map_ofNat,map_one]
  ring

theorem iteratedDeriv_thetaMode (m n : ℕ) :
    iteratedDeriv n (thetaMode m) = thetaModeDerivative m n := by
  induction n with
  | zero => funext u; simp [thetaModeDerivative,thetaDerivativePolynomial]
  | succ n hn =>
    rw [iteratedDeriv_succ,hn]
    funext u
    exact (hasDerivAt_thetaModeDerivative m n u).deriv

theorem contDiff_thetaMode (m : ℕ) (n : ℕ) : ContDiff ℝ n (thetaMode m) := by
  unfold thetaMode XiThetaCosine.thetaTailMode
  fun_prop

/-- This is the precise Mathlib mean-remainder convention: denominator n!,
not (n+1)!. It matches the conservative certificate already used. -/
theorem thetaMode_taylor_remainder (m n : ℕ) (a b C x : ℝ)
    (hab : a < b) (hx : x ∈ Icc a b)
    (hC : ∀ y ∈ Icc a b, |thetaModeDerivative m (n+1) y| ≤ C) :
    |thetaMode m x-taylorWithinEval (thetaMode m) n (Icc a b) a x| ≤
      C*(x-a)^(n+1)/(n.factorial:ℝ) := by
  have hf := contDiff_thetaMode m (n+1)
  have h := taylor_mean_remainder_bound (n:=n) hab.le hf.contDiffOn hx (by
    intro y hy
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hab)
      hf.contDiffAt hy,iteratedDeriv_thetaMode,Real.norm_eq_abs]
    exact hC y hy)
  simpa only [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hx.1),
    mul_div_assoc] using h

/-- Absolute-coefficient majorant. Signed source coefficients are retained
in the Taylor polynomial; this is used only for its error bound. -/
def thetaDerivativeMajorant (n : ℕ) (Q : ℝ) : ℝ :=
  ∑ i ∈ Finset.range ((thetaDerivativePolynomial n).natDegree+1),
    |((thetaDerivativePolynomial n).coeff i:ℝ)| *Q^i

theorem thetaDerivativePolynomial_abs_le (n : ℕ) {q Q : ℝ}
    (hq : 0 ≤ q) (hqQ : q ≤ Q) :
    |aeval q (thetaDerivativePolynomial n)| ≤ thetaDerivativeMajorant n Q := by
  rw [aeval_eq_sum_range]
  change |∑ i ∈ Finset.range _,
    ((thetaDerivativePolynomial n).coeff i:ℝ)*q^i| ≤ _
  calc
    _ ≤ ∑ i ∈ Finset.range _, |((thetaDerivativePolynomial n).coeff i:ℝ)*q^i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul,abs_pow,abs_of_nonneg hq]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq hqQ i) (abs_nonneg _)

theorem thetaMode_nonneg (m : ℕ) (u : ℝ) : 0 ≤ thetaMode m u := by
  unfold thetaMode XiThetaCosine.thetaTailMode
  positivity

theorem thetaMode_antitone (m : ℕ) : AntitoneOn (thetaMode m) (Ici 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    ((contDiff_thetaMode m 1).continuous.continuousOn)
  · intro u _
    exact (hasDerivAt_thetaMode m u).differentiableAt.differentiableWithinAt
  · intro u hu
    have hu0 : 0 ≤ u := interior_subset hu
    rw [(hasDerivAt_thetaMode m u).deriv]
    have hm : (1:ℝ) ≤ ((m+1:ℕ):ℝ)^2 := by
      have h : (1:ℝ) ≤ ((m+1:ℕ):ℝ) := by exact_mod_cast (show 1 ≤ m+1 by omega)
      nlinarith
    have he : 1 ≤ exp (2*u) := one_le_exp_iff.mpr (by positivity)
    have hq : 3 ≤ thetaArgument m u := by
      unfold thetaArgument
      calc
        (3:ℝ) = 3*1*1 := by ring
        _ ≤ Real.pi*((m+1:ℕ):ℝ)^2*exp (2*u) := by gcongr; exact Real.pi_gt_three.le
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (thetaMode_nonneg m u)

theorem thetaModeDerivative_cell_bound (m n : ℕ) (a b Q U : ℝ)
    (ha : 0 ≤ a) (hQ : thetaArgument m b ≤ Q)
    (hU : thetaMode m a ≤ U) :
    ∀ x ∈ Icc a b, |thetaModeDerivative m n x| ≤ thetaDerivativeMajorant n Q*U := by
  intro x hx
  have hq : 0 ≤ thetaArgument m x := by unfold thetaArgument; positivity
  have hqx : thetaArgument m x ≤ Q := by
    apply le_trans _ hQ
    unfold thetaArgument
    gcongr
    exact hx.2
  have hp := thetaDerivativePolynomial_abs_le n hq hqx
  have hf : thetaMode m x ≤ U :=
    (thetaMode_antitone m ha (ha.trans hx.1) hx.1).trans hU
  unfold thetaModeDerivative
  rw [abs_mul,abs_of_nonneg (thetaMode_nonneg m x)]
  apply mul_le_mul hp hf (thetaMode_nonneg m x)
  exact (abs_nonneg _).trans hp

/-- Explicit source derivatives, rather than within-derivative placeholders. -/
theorem thetaMode_taylor_eq_sum (m n : ℕ) (a b x : ℝ) (hab : a < b) :
    taylorWithinEval (thetaMode m) n (Icc a b) a x =
      ∑ r ∈ Finset.range (n+1),
        thetaModeDerivative m r a/(r.factorial:ℝ)*(x-a)^r := by
  rw [taylor_within_apply]
  apply Finset.sum_congr rfl
  intro r _
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hab)
    (contDiff_thetaMode m r).contDiffAt ⟨le_rfl,hab.le⟩,iteratedDeriv_thetaMode]
  simp only [smul_eq_mul,div_eq_mul_inv]
  ring

end
end CarryIntegralCertificate
