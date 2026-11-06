import SigmaC5SourceAnalytic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

/-!
# Explicit analytic modulus bounds for the original C5 source

The source remains the completed native characteristic and its exact displaced
product.  This file starts the numerical majorant by bounding the original
complex Gamma factor on the compact strip used by the Cauchy disk.
-/

namespace CarrySigmaObstruction

open CarrySelfAdjointOperator
open CarrySelfAdjointOperator.CompletedNativeRealHPCarrierCertificate
open NativeCarrySpectralWeyl.Camera
open FiniteNativeCarryOperator.Camera
open MeasureTheory Set
open scoped BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

private theorem gamma_shift_norm_le_five {z : ℂ}
    (hz0 : 0 < z.re) (hz1 : z.re ≤ 1) :
    ‖Complex.Gamma (z + 1)‖ ≤ 5 := by
  let f : ℝ → ℂ := fun x => (Real.exp (-x) : ℂ) * (x : ℂ) ^ z
  have hf : IntegrableOn f (Ioi 0) := by
    have h := Complex.GammaIntegral_convergent (s := z + 1) (by
      simp only [Complex.add_re, Complex.one_re]
      linarith)
    convert h using 1 with x
    simp [f]
  have hsplit : Complex.GammaIntegral (z + 1) =
      (∫ x in Ioc (0 : ℝ) 1, f x) + (∫ x in Ioi (1 : ℝ), f x) := by
    rw [Complex.GammaIntegral,
      ← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
        (hf.mono_set Ioc_subset_Ioi_self)
        (hf.mono_set (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))),
      Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)]
    congr 1
    funext x
    simp [f]
  have hfirst : ‖∫ x in Ioc (0 : ℝ) 1, f x‖ ≤ 1 := by
    have hbound : ∀ᵐ x ∂(volume.restrict (Ioc (0 : ℝ) 1)), ‖f x‖ ≤ 1 := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      have hx0 : 0 < x := hx.1
      have hx1 : x ≤ 1 := hx.2
      change ‖(Real.exp (-x) : ℂ) * (x : ℂ) ^ z‖ ≤ 1
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0,
        Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
      have hexp : 0 ≤ Real.exp (-x) ∧ Real.exp (-x) ≤ 1 := by
        constructor
        · exact (Real.exp_pos _).le
        · exact Real.exp_le_one_iff.mpr (by linarith)
      have hpow : 0 ≤ x ^ z.re ∧ x ^ z.re ≤ 1 := by
        constructor
        · exact Real.rpow_nonneg hx0.le _
        · exact Real.rpow_le_one hx0.le hx1 (by linarith)
      exact (mul_le_one₀ hexp.2 hpow.1 hpow.2)
    calc
      ‖∫ x in Ioc (0 : ℝ) 1, f x‖ ≤
          1 * (volume.restrict (Ioc (0 : ℝ) 1)).real univ := by
            exact norm_integral_le_of_norm_le_const hbound
      _ = 1 := by simp [Real.volume_real_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have htail : ‖∫ x in Ioi (1 : ℝ), f x‖ ≤ 4 := by
    have hg : Integrable (fun x : ℝ => 2 * Real.exp (-(1 / 2 : ℝ) * x))
        (volume.restrict (Ioi (1 : ℝ))) := by
      exact (integrableOn_exp_mul_Ioi (by norm_num : -(1 / 2 : ℝ) < 0) 1).const_mul 2
    have hpoint : ∀ᵐ x ∂(volume.restrict (Ioi (1 : ℝ))),
        ‖f x‖ ≤ 2 * Real.exp (-(1 / 2 : ℝ) * x) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx1 : 1 ≤ x := le_of_lt hx
      change ‖(Real.exp (-x) : ℂ) * (x : ℂ) ^ z‖ ≤
        2 * Real.exp (-(1 / 2 : ℝ) * x)
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < x),
        Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
      have hpow : x ^ z.re ≤ x := by
        simpa only [Real.rpow_one] using
          (Real.rpow_le_rpow_of_exponent_le hx1 hz1)
      have hexp : x ≤ 2 * Real.exp (x / 2) := by
        have h := Real.add_one_le_exp (x / 2)
        nlinarith
      have hmain : Real.exp (-x) * x ≤ 2 * Real.exp (-(1 / 2 : ℝ) * x) := by
        have hmul := mul_le_mul_of_nonneg_left hexp (Real.exp_pos (-x)).le
        have hexpid : Real.exp (-x) * (2 * Real.exp (x / 2)) =
            2 * Real.exp (-(1 / 2 : ℝ) * x) := by
          calc
            Real.exp (-x) * (2 * Real.exp (x / 2)) =
                2 * (Real.exp (-x) * Real.exp (x / 2)) := by ring
            _ = 2 * Real.exp (-x + x / 2) := by rw [← Real.exp_add]
            _ = 2 * Real.exp (-(1 / 2 : ℝ) * x) := by
              have harg : -x + x / 2 = -(1 / 2 : ℝ) * x := by ring
              rw [harg]
        rw [hexpid] at hmul
        exact hmul
      exact le_trans (mul_le_mul_of_nonneg_left hpow (Real.exp_pos (-x)).le) hmain
    calc
      ‖∫ x in Ioi (1 : ℝ), f x‖ ≤
          ∫ x in Ioi (1 : ℝ), 2 * Real.exp (-(1 / 2 : ℝ) * x) :=
            norm_integral_le_of_norm_le hg hpoint
      _ = 4 * Real.exp (-(1 / 2 : ℝ)) := by
          rw [integral_const_mul, integral_exp_mul_Ioi (by norm_num) 1]
          norm_num [div_eq_mul_inv]
          ring_nf
      _ ≤ 4 := by
          calc
            4 * Real.exp (-(1 / 2 : ℝ)) ≤ 4 * 1 := by
              gcongr
              exact Real.exp_le_one_iff.mpr (by norm_num)
            _ = 4 := by ring
  have hG : ‖Complex.Gamma (z + 1)‖ = ‖Complex.GammaIntegral (z + 1)‖ := by
    rw [Complex.Gamma_eq_integral (by simp only [Complex.add_re, Complex.one_re]; linarith)]
  rw [hG, hsplit]
  calc
    ‖(∫ x in Ioc (0 : ℝ) 1, f x) + ∫ x in Ioi (1 : ℝ), f x‖ ≤
        ‖∫ x in Ioc (0 : ℝ) 1, f x‖ + ‖∫ x in Ioi (1 : ℝ), f x‖ := norm_add_le _ _
    _ ≤ 5 := by linarith

theorem complexGamma_norm_le_100 {z : ℂ}
    (hzlo : (1 / 20 : ℝ) ≤ z.re) (hzhi : z.re ≤ 1 / 2) :
    ‖Complex.Gamma z‖ ≤ 100 := by
  have hzpos : 0 < z.re := by linarith
  have hzne : z ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp at hr
    linarith
  have hrec := Complex.Gamma_add_one z hzne
  have hshift := gamma_shift_norm_le_five hzpos (by linarith)
  have hmul : ‖Complex.Gamma z‖ * ‖z‖ ≤ 5 := by
    calc
      ‖Complex.Gamma z‖ * ‖z‖ = ‖z * Complex.Gamma z‖ := by rw [norm_mul]; ring
      _ = ‖Complex.Gamma (z + 1)‖ := by rw [← hrec]
      _ ≤ 5 := hshift
  have hnormre : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
  have hzlower : (1 / 20 : ℝ) ≤ ‖z‖ := by
    calc
      (1 / 20 : ℝ) ≤ z.re := hzlo
      _ = |z.re| := by rw [abs_of_pos hzpos]
      _ ≤ ‖z‖ := hnormre
  have hnonneg : 0 ≤ ‖Complex.Gamma z‖ := norm_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hzlower hnonneg]

theorem complexGamma_norm_le_1000 {z : ℂ}
    (hzlo : (1 / 200 : ℝ) ≤ z.re) (hzhi : z.re ≤ 1 / 2) :
    ‖Complex.Gamma z‖ ≤ 1000 := by
  have hzpos : 0 < z.re := by linarith
  have hzne : z ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp at hr
    linarith
  have hrec := Complex.Gamma_add_one z hzne
  have hshift := gamma_shift_norm_le_five hzpos (by linarith)
  have hmul : ‖Complex.Gamma z‖ * ‖z‖ ≤ 5 := by
    calc
      ‖Complex.Gamma z‖ * ‖z‖ = ‖z * Complex.Gamma z‖ := by rw [norm_mul]; ring
      _ = ‖Complex.Gamma (z + 1)‖ := by rw [← hrec]
      _ ≤ 5 := hshift
  have hnormre : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
  have hzlower : (1 / 200 : ℝ) ≤ ‖z‖ := by
    calc
      (1 / 200 : ℝ) ≤ z.re := hzlo
      _ = |z.re| := by rw [abs_of_pos hzpos]
      _ ≤ ‖z‖ := hnormre
  have hnonneg : 0 ≤ ‖Complex.Gamma z‖ := norm_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hzlower hnonneg]

private theorem c5_inv_sq_sum_range_le (n : ℕ) :
    (∑ k ∈ Finset.range n, ((k + 1 : ℝ) ^ 2)⁻¹) ≤ 2 := by
  by_cases hn : 0 < n
  · have hsum :
        (∑ k ∈ Finset.range n, ((k + 1 : ℝ) ^ 2)⁻¹) =
          1 + ∑ i ∈ Finset.Ioo 1 (n + 1), ((i : ℝ) ^ 2)⁻¹ := by
      have hIco :
          (∑ k ∈ Finset.range n, ((k + 1 : ℝ) ^ 2)⁻¹) =
            ∑ i ∈ Finset.Ico 1 (n + 1), ((i : ℝ) ^ 2)⁻¹ := by
        rw [Finset.sum_Ico_eq_sum_range]
        simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, add_comm]
      have hset : Finset.Ico 1 (n + 1) = insert 1 (Finset.Ioo 1 (n + 1)) := by
        ext i
        simp only [Finset.mem_Ico, Finset.mem_insert, Finset.mem_Ioo]
        omega
      rw [hIco, hset, Finset.sum_insert]
      · norm_num
      · simp
    rw [hsum]
    have htail := sum_Ioo_inv_sq_le (α := ℝ) 1 (n + 1)
    have htail' :
        (∑ i ∈ Finset.Ioo 1 (n + 1), ((i : ℝ) ^ 2)⁻¹) ≤ 1 := by
      norm_num at htail
      simpa using htail
    calc
      1 + ∑ i ∈ Finset.Ioo 1 (n + 1), ((i : ℝ) ^ 2)⁻¹ =
          (∑ i ∈ Finset.Ioo 1 (n + 1), ((i : ℝ) ^ 2)⁻¹) + 1 := by ring
      _ ≤ 1 + 1 := add_le_add_left htail' (1 : ℝ)
      _ = 2 := by norm_num
  · have hn0 : n = 0 := by omega
    simp [hn0]

private def c5InvSq (n : ℕ) : ℝ := (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹

private theorem c5InvSq_summable : Summable c5InvSq := by
  apply summable_of_sum_range_le (f := c5InvSq)
  · intro n
    exact inv_nonneg.mpr (sq_nonneg _)
  · intro n
    simpa [c5InvSq] using c5_inv_sq_sum_range_le n

private theorem c5InvSq_tsum_le_two : (∑' n, c5InvSq n) ≤ 2 := by
  apply Real.tsum_le_of_sum_range_le (f := c5InvSq)
  · intro n
    exact inv_nonneg.mpr (sq_nonneg _)
  · intro n
    simpa [c5InvSq] using c5_inv_sq_sum_range_le n

private theorem c5_bracketCameraThree_norm_le_nine {s : ℂ}
    (hsre : 0 ≤ s.re) (hsprod : ‖s * (s + 1)‖ ≤ 4) :
    ‖bracketCharacteristic 3 s‖ ≤ 9 := by
  have hseed : seedDirichletTerm 3 s = 1 := by
    norm_num [seedDirichletTerm, dirichletValue, radiusSet, halfRange]
  have hterms : ∀ n, ‖centerBracketTerm 3 s n‖ ≤ 4 * c5InvSq n := by
    intro n
    have h := centerBracketTerm_norm_le_majorant
      (camera := 3) (by norm_num) (s := s) (sigma := 0) (bound := 4)
      (by linarith) hsprod (by norm_num) n
    have heq : centerBracketMajorant 3 0 4 n = 4 * c5InvSq n := by
      norm_num [centerBracketMajorant, radiusBracketMajorant, c5InvSq,
        radiusSet, halfRange]
      rfl
    rw [heq] at h
    exact h
  have hnorms : Summable (fun n => ‖centerBracketTerm 3 s n‖) :=
    centerBracketTerm_norm_summable (camera := 3) (by norm_num) (by linarith)
  have hmaj : Summable (fun n => 4 * c5InvSq n) := c5InvSq_summable.mul_left 4
  have hsum :
      (∑' n, ‖centerBracketTerm 3 s n‖) ≤ ∑' n, 4 * c5InvSq n :=
    hnorms.tsum_le_tsum hterms hmaj
  have hsum8 : (∑' n, 4 * c5InvSq n) ≤ 8 := by
    calc
      (∑' n, 4 * c5InvSq n) = 4 * (∑' n, c5InvSq n) := by rw [ tsum_mul_left ]
      _ ≤ 4 * 2 := by gcongr; exact c5InvSq_tsum_le_two
      _ = 8 := by norm_num
  calc
    ‖bracketCharacteristic 3 s‖ = ‖seedDirichletTerm 3 s +
        ∑' n, centerBracketTerm 3 s n‖ := by rfl
    _ ≤ ‖seedDirichletTerm 3 s‖ +
        ‖∑' n, centerBracketTerm 3 s n‖ := norm_add_le _ _
    _ ≤ 1 + ∑' n, ‖centerBracketTerm 3 s n‖ := by
      rw [hseed, norm_one]
      gcongr
      exact norm_tsum_le_tsum_norm hnorms
    _ ≤ 1 + 8 := by linarith [hsum.trans hsum8]
    _ = 9 := by norm_num

private theorem c5_factorThree_norm_lower {s : ℂ}
    (hshi : s.re ≤ 99 / 100) :
    (1 / 100 : ℝ) ≤ ‖factor 3 s‖ := by
  have hlog : (1 : ℝ) ≤ Real.log 3 := by
    apply (Real.le_log_iff_exp_le (by norm_num : 0 < (3 : ℝ))).2
    have h := Real.exp_one_lt_d9
    norm_num at h ⊢
    linarith
  have hbase : (101 / 100 : ℝ) ≤ (3 : ℝ) ^ (1 / 100 : ℝ) := by
    calc
      (101 / 100 : ℝ) ≤ 1 + Real.log 3 / 100 := by nlinarith
      _ ≤ Real.exp (Real.log 3 / 100) := by
        have h := Real.add_one_le_exp (Real.log 3 / 100)
        linarith
      _ = (3 : ℝ) ^ (1 / 100 : ℝ) := by
        rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
        congr 1
        ring
  have hexp : (1 / 100 : ℝ) ≤ 1 - s.re := by linarith
  have hpowReal : (101 / 100 : ℝ) ≤ (3 : ℝ) ^ (1 - s.re) :=
    hbase.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp)
  have hpowNorm : (101 / 100 : ℝ) ≤ ‖(3 : ℂ) ^ (1 - s)‖ := by
    change (101 / 100 : ℝ) ≤ ‖((3 : ℝ) : ℂ) ^ (1 - s)‖
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 3)]
    simpa using hpowReal
  have hrev := norm_sub_norm_le ((3 : ℂ) ^ (1 - s)) (1 : ℂ)
  have hpowden : (1 / 100 : ℝ) ≤ ‖(3 : ℂ) ^ (1 - s) - 1‖ := by
    rw [norm_one] at hrev
    have h := hrev
    have hpos : (0 : ℝ) ≤ ‖(3 : ℂ) ^ (1 - s)‖ - 1 := by linarith
    calc
      (1 / 100 : ℝ) ≤ ‖(3 : ℂ) ^ (1 - s)‖ - 1 := by linarith
      _ ≤ ‖(3 : ℂ) ^ (1 - s) - 1‖ := h
  have hden : (1 / 100 : ℝ) ≤ ‖1 - (3 : ℂ) ^ (1 - s)‖ := by
    simpa only [norm_sub_rev] using hpowden
  have hfactor : factor 3 s = 1 - (3 : ℂ) ^ (1 - s) := by
    rw [factor_of_odd (by decide : 3 ≠ 2) (by decide : Odd 3)]
    rfl
  rw [hfactor]
  exact hden

private theorem c5_nativeScalar_norm_le_900 {s : ℂ}
    (hslo : (1 / 100 : ℝ) ≤ s.re) (hshi : s.re ≤ 99 / 100)
    (hsprod : ‖s * (s + 1)‖ ≤ 4) :
    ‖nativeScalar s‖ ≤ 900 := by
  have hbracket := c5_bracketCameraThree_norm_le_nine (by linarith) hsprod
  have hfactor := c5_factorThree_norm_lower hshi
  have hfactorpos : 0 < ‖factor 3 s‖ := lt_of_lt_of_le (by norm_num) hfactor
  rw [nativeScalar, norm_div]
  apply (div_le_iff₀ hfactorpos).2
  have hmul := mul_le_mul_of_nonneg_left hfactor (by norm_num : (0 : ℝ) ≤ 900)
  norm_num at hmul
  nlinarith

private theorem c5_source_parameter_region {w : ℂ}
    (hwre : |w.re| ≤ 39 / 100) (hwim : |w.im| ≤ 49 / 100) :
    (1 / 100 : ℝ) ≤ (operatorHeightParameter w).re ∧
      (operatorHeightParameter w).re ≤ 99 / 100 ∧
      |(operatorHeightParameter w).im| ≤ 1 / 2 := by
  have hre := abs_le.mp hwre
  have him := abs_le.mp hwim
  have hpre : (operatorHeightParameter w).re = 1 / 2 - w.im := by
    simp [operatorHeightParameter]
    ring
  have hpim : (operatorHeightParameter w).im = w.re := by
    simp [operatorHeightParameter]
  refine ⟨?_, ?_, ?_⟩
  · rw [hpre]
    norm_num
    linarith [him.2]
  · rw [hpre]
    norm_num
    linarith [him.1]
  · rw [hpim]
    exact le_trans hwre (by norm_num)

private theorem c5_s_times_splusone_norm_le_four {s : ℂ}
    (hslo : (1 / 100 : ℝ) ≤ s.re) (hshi : s.re ≤ 99 / 100)
    (hsim : |s.im| ≤ 1 / 2) :
    ‖s * (s + 1)‖ ≤ 4 := by
  have hreal : |s.re| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hrealPlus : |(s + 1).re| ≤ 2 := by
    simp only [Complex.add_re, Complex.one_re]
    rw [abs_le]
    constructor <;> linarith [abs_le.mp hreal]
  have hsNorm : ‖s‖ ≤ (3 / 2 : ℝ) := by
    calc
      ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
      _ ≤ 1 + 1 / 2 := add_le_add hreal hsim
      _ = 3 / 2 := by norm_num
  have hsplusNorm : ‖s + 1‖ ≤ (5 / 2 : ℝ) := by
    calc
      ‖s + 1‖ ≤ |(s + 1).re| + |(s + 1).im| :=
        Complex.norm_le_abs_re_add_abs_im (s + 1)
      _ ≤ 2 + 1 / 2 := add_le_add hrealPlus (by simpa using hsim)
      _ = 5 / 2 := by norm_num
  rw [norm_mul]
  calc
    ‖s‖ * ‖s + 1‖ ≤ (3 / 2 : ℝ) * (5 / 2 : ℝ) := by gcongr
    _ ≤ 4 := by norm_num

private theorem c5_nativeXi_norm_le_2000 {z : ℂ}
    (hslo : (1 / 100 : ℝ) ≤ (operatorHeightParameter z).re)
    (hshi : (operatorHeightParameter z).re ≤ 99 / 100)
    (hsim : |(operatorHeightParameter z).im| ≤ 1 / 2) :
    ‖nativeXiCompletionFactor z‖ ≤ 2000 := by
  let s : ℂ := operatorHeightParameter z
  have hslo' : (1 / 100 : ℝ) ≤ s.re := hslo
  have hshi' : s.re ≤ 99 / 100 := hshi
  have hsim' : |s.im| ≤ 1 / 2 := hsim
  have hprod := c5_s_times_splusone_norm_le_four hslo' hshi' hsim'
  have hsNorm : ‖s‖ ≤ 3 / 2 := by
    calc
      ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
      _ ≤ 1 + 1 / 2 := by
        apply add_le_add _ hsim'
        exact abs_le.mpr ⟨by linarith, by linarith⟩
      _ = 3 / 2 := by norm_num
  have hsSubNorm : ‖s - 1‖ ≤ 3 / 2 := by
    calc
      ‖s - 1‖ ≤ |(s - 1).re| + |(s - 1).im| :=
        Complex.norm_le_abs_re_add_abs_im (s - 1)
      _ ≤ 1 + 1 / 2 := by
        have hsubre : |(s - 1).re| ≤ 1 := by
          simp only [Complex.sub_re, Complex.one_re]
          rw [abs_le]
          constructor <;> linarith
        have hsubim : |(s - 1).im| ≤ 1 / 2 := by
          simpa only [Complex.sub_im, Complex.one_im, sub_zero] using hsim'
        exact add_le_add hsubre hsubim
      _ = 3 / 2 := by norm_num
  have hlogpi : 0 < Real.log Real.pi := Real.log_pos (by linarith [Real.pi_gt_three])
  have hexpRe :
      (-(s / 2) * (Real.log Real.pi : ℂ)).re =
        -(s.re / 2) * Real.log Real.pi := by
    simp [Complex.mul_re]
  have hexpNorm :
      ‖Complex.exp (-(s / 2) * (Real.log Real.pi : ℂ))‖ ≤ 1 := by
    rw [Complex.norm_exp, hexpRe]
    apply Real.exp_le_one_iff.mpr
    have hspos : 0 ≤ s.re / 2 := by linarith
    nlinarith [mul_nonneg hspos hlogpi.le]
  have hgamma : ‖Complex.Gamma (s / 2)‖ ≤ 1000 := by
    apply complexGamma_norm_le_1000
    · have hdiv : (s / 2).re = s.re / 2 := by simp
      rw [hdiv]
      linarith
    · have hdiv : (s / 2).re = s.re / 2 := by simp
      rw [hdiv]
      linarith
  have hfactorNorm :
      ‖nativeXiCompletionFactor z‖ =
        (1 / 2 : ℝ) * ‖s‖ * ‖s - 1‖ *
          ‖Complex.exp (-(s / 2) * (Real.log Real.pi : ℂ))‖ *
            ‖Complex.Gamma (s / 2)‖ := by
    simp [nativeXiCompletionFactor, s, operatorHeightParameter]
  rw [hfactorNorm]
  calc
    (1 / 2 : ℝ) * ‖s‖ * ‖s - 1‖ *
        ‖Complex.exp (-(s / 2) * (Real.log Real.pi : ℂ))‖ *
          ‖Complex.Gamma (s / 2)‖ ≤
      (1 / 2 : ℝ) * (3 / 2) * (3 / 2) * 1 * 1000 := by
        gcongr
    _ ≤ 2000 := by norm_num

private theorem c5_completedCharacteristic_norm_le_twoMillion {z : ℂ}
    (hslo : (1 / 100 : ℝ) ≤ (operatorHeightParameter z).re)
    (hshi : (operatorHeightParameter z).re ≤ 99 / 100)
    (hsim : |(operatorHeightParameter z).im| ≤ 1 / 2) :
    ‖completedNativeOperatorCharacteristic z‖ ≤ 2000000 := by
  have hsprod := c5_s_times_splusone_norm_le_four hslo hshi hsim
  have hxi := c5_nativeXi_norm_le_2000 hslo hshi hsim
  have hscalar := c5_nativeScalar_norm_le_900 hslo hshi hsprod
  rw [completedNativeOperatorCharacteristic, norm_mul]
  calc
    ‖nativeXiCompletionFactor z‖ *
        ‖nativeScalar (operatorHeightParameter z)‖ ≤ 2000 * 900 :=
          mul_le_mul hxi hscalar (norm_nonneg _) (by norm_num)
    _ ≤ 2000000 := by norm_num

theorem displacedProductC_norm_le_10pow13_on_ball_39
    (d : ℝ) (hd : |d| ≤ (1 / 10 : ℝ)) {z : ℂ}
    (hz : z ∈ Metric.ball 0 (39 / 100 : ℝ)) :
    ‖displacedProductC d z‖ ≤ (10 : ℝ) ^ 13 := by
  have hnorm : ‖z‖ < (39 / 100 : ℝ) := by
    simpa [Metric.mem_ball, dist_zero_right] using hz
  have him : |z.im| < 39 / 100 := (Complex.abs_im_le_norm z).trans_lt hnorm
  have hre : |z.re| < 39 / 100 := (Complex.abs_re_le_norm z).trans_lt hnorm
  have hminusIm : |(z - Complex.I * (d : ℂ)).im| ≤ 49 / 100 := by
    calc
      |(z - Complex.I * (d : ℂ)).im| = |z.im - d| := by simp
      _ ≤ |z.im| + |d| := abs_sub _ _
      _ ≤ 39 / 100 + 1 / 10 := by linarith [him, hd]
      _ ≤ 49 / 100 := by norm_num
  have hplusIm : |(z + Complex.I * (d : ℂ)).im| ≤ 49 / 100 := by
    calc
      |(z + Complex.I * (d : ℂ)).im| = |z.im + d| := by simp
      _ ≤ |z.im| + |d| := abs_add_le _ _
      _ ≤ 39 / 100 + 1 / 10 := by linarith [him, hd]
      _ ≤ 49 / 100 := by norm_num
  have hminusRe : |(z - Complex.I * (d : ℂ)).re| ≤ 39 / 100 := by
    simpa using (le_of_lt hre)
  have hplusRe : |(z + Complex.I * (d : ℂ)).re| ≤ 39 / 100 := by
    simpa using (le_of_lt hre)
  obtain ⟨hml, hmu, hmi⟩ := c5_source_parameter_region hminusRe hminusIm
  obtain ⟨hpl, hpu, hpi⟩ := c5_source_parameter_region hplusRe hplusIm
  have hminus := c5_completedCharacteristic_norm_le_twoMillion hml hmu hmi
  have hplus := c5_completedCharacteristic_norm_le_twoMillion hpl hpu hpi
  change ‖completedNativeOperatorCharacteristic
      (z - Complex.I * (d : ℂ)) *
      completedNativeOperatorCharacteristic (z + Complex.I * (d : ℂ))‖ ≤
    (10 : ℝ) ^ 13
  rw [norm_mul]
  calc
    ‖completedNativeOperatorCharacteristic (z - Complex.I * (d : ℂ))‖ *
        ‖completedNativeOperatorCharacteristic (z + Complex.I * (d : ℂ))‖ ≤
      2000000 * 2000000 :=
        mul_le_mul hminus hplus (norm_nonneg _) (by norm_num)
    _ ≤ (10 : ℝ) ^ 13 := by norm_num

theorem displacedProductC_norm_le_10pow100_on_ball_39
    (d : ℝ) (hd : |d| ≤ (1 / 10 : ℝ)) {z : ℂ}
    (hz : z ∈ Metric.ball 0 (39 / 100 : ℝ)) :
    ‖displacedProductC d z‖ ≤ (10 : ℝ) ^ 100 := by
  exact (displacedProductC_norm_le_10pow13_on_ball_39 d hd hz).trans (by norm_num)

#print axioms complexGamma_norm_le_100
#print axioms complexGamma_norm_le_1000
#print axioms displacedProductC_norm_le_10pow13_on_ball_39
#print axioms displacedProductC_norm_le_10pow100_on_ball_39

end
end CarrySigmaObstruction
