import NativeGammaJets
import Mathlib.Analysis.Calculus.Deriv.ZPow

namespace CarryC3Gamma
open CarrySelfAdjointOperator PhysicalSewing CarryTwoEvenJets
open Set Filter Topology
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 5000

theorem jet_mul {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) (n : ℕ) :
    sourceJet n (fun w => f w*g w) =
      ∑ j ∈ Finset.range (n+1), sourceJet j f*sourceJet (n-j) g := by
  unfold sourceJet
  change iteratedDeriv n (f*g) 0/(n.factorial:ℂ) = _
  rw [iteratedDeriv_mul hf.contDiffAt hg.contDiffAt,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Nat.cast_choose ℂ (Nat.le_of_lt_succ (Finset.mem_range.mp hj))]
  have hn : (n.factorial:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hj0 : (j.factorial:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have hnj : ((n-j).factorial:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n-j)
  field_simp

theorem jet_inv_affine (r : ℕ) (c a : ℂ) :
    sourceJet r (fun w => (c*w+a)⁻¹) = (-c)^r/a^(r+1) := by
  unfold sourceJet
  rw [iteratedDeriv_eq_iterate,iter_deriv_inv_linear]
  simp only [mul_zero,zero_add]
  rw [show (-1-(r:ℤ)) = -((r+1:ℕ):ℤ) by omega,zpow_neg,zpow_natCast]
  have hr : (r.factorial:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
  rw [neg_pow]
  field_simp
  ring

theorem jet_exp_linear (r : ℕ) (c : ℂ) :
    sourceJet r (fun w => Complex.exp (c*w)) = c^r/(r.factorial:ℂ) := by
  simp [sourceJet,iteratedDeriv_cexp_const_mul]

theorem jet_sum (N r : ℕ) (f : ℕ → ℂ → ℂ)
    (hf : ∀ k ∈ Finset.range N, AnalyticAt ℂ (f k) 0) :
    sourceJet r (fun w => ∑ k ∈ Finset.range N, f k w) =
      ∑ k ∈ Finset.range N, sourceJet r (f k) := by
  unfold sourceJet
  have he : (fun w => ∑ k ∈ Finset.range N, f k w) = ∑ k ∈ Finset.range N, f k := by
    ext w
    simp only [Finset.sum_apply]
  rw [he]
  rw [iteratedDeriv_sum (fun k hk => (hf k hk).contDiffAt),Finset.sum_div]

theorem jet_const_mul (r : ℕ) (c : ℂ) (f : ℂ → ℂ) :
    sourceJet r (fun w => c*f w) = c*sourceJet r f := by
  simp only [sourceJet,iteratedDeriv_const_mul_field]
  ring

theorem native_gamma_power_formula (w : ℂ) :
    (81:ℂ)^(operatorHeightParameter w/2) =
      3*Complex.exp ((2*Complex.I*(Real.log 3:ℂ))*w) := by
  have hl : Complex.log 81 = 4*(Real.log 3:ℂ) := by
    change Complex.log ((81:ℝ):ℂ) = _
    rw [← Complex.ofReal_log (by norm_num : (0:ℝ)≤81),
      show (81:ℝ)=3^4 by norm_num,Real.log_pow]
    push_cast
    rfl
  rw [Complex.cpow_def_of_ne_zero (by norm_num : (81:ℂ)≠0),hl]
  have he : 4*(Real.log 3:ℂ)*(operatorHeightParameter w/2) =
      (Real.log 3:ℂ)+(2*Complex.I*(Real.log 3:ℂ))*w := by
    unfold operatorHeightParameter
    ring
  rw [he,Complex.exp_add,← Complex.ofReal_exp,Real.exp_log (by norm_num : (0:ℝ)<3)]
  norm_num

/-- Exact rational sums; large alternating terms are combined BEFORE rounding. -/
def rationalCoefficient (N r : ℕ) : ℚ :=
  ∑ k ∈ Finset.range N, (-81:ℚ)^k/((k.factorial:ℚ)*((k:ℚ)+1/4)^(r+1))

def gammaCoefficient (r : ℕ) (L : ℝ) : ℂ :=
  3*Complex.I^r*∑ j ∈ Finset.range (r+1),
    ((2*L:ℝ):ℂ)^j/(j.factorial:ℂ)*(-1/2:ℂ)^(r-j)*
      (rationalCoefficient 512 (r-j):ℂ)

theorem finite_native_gamma_formula (w : ℂ) :
    finiteNativeGamma w = 3*(Complex.exp ((2*Complex.I*(Real.log 3:ℂ))*w)*
      ∑ k ∈ Finset.range 512,
        ((-81:ℂ)^k/(k.factorial:ℂ))*((Complex.I/2)*w+((k:ℂ)+1/4))⁻¹) := by
  unfold finiteNativeGamma gammaFinite
  norm_num only [Complex.ofReal_ofNat]
  rw [native_gamma_power_formula]
  rw [mul_assoc]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have he : operatorHeightParameter w/2+(k:ℂ) =
      (Complex.I/2)*w+((k:ℂ)+1/4) := by unfold operatorHeightParameter; ring
  rw [he]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

theorem finite_native_gamma_coefficient (r : ℕ) :
    sourceJet r finiteNativeGamma = gammaCoefficient r (Real.log 3) := by
  have he : finiteNativeGamma = fun w =>
      3*(Complex.exp ((2*Complex.I*(Real.log 3:ℂ))*w)*
      ∑ k ∈ Finset.range 512,
        ((-81:ℂ)^k/(k.factorial:ℂ))*((Complex.I/2)*w+((k:ℂ)+1/4))⁻¹) :=
    funext finite_native_gamma_formula
  have hi (k : ℕ) : AnalyticAt ℂ
      (fun w => ((-81:ℂ)^k/(k.factorial:ℂ))*((Complex.I/2)*w+((k:ℂ)+1/4))⁻¹) 0 := by
    apply analyticAt_const.mul
    apply AnalyticAt.inv (by fun_prop)
    norm_num
    have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
    intro hh
    have hr := congrArg Complex.re hh
    norm_num at hr
    linarith
  rw [he,jet_const_mul,jet_mul (by fun_prop) (Finset.analyticAt_fun_sum _ (fun k _ => hi k))]
  simp only [jet_exp_linear,jet_sum _ _ _ (fun k _ => hi k),jet_const_mul,jet_inv_affine]
  unfold gammaCoefficient rationalCoefficient
  push_cast
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  have hjle : j ≤ r := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hI : Complex.I^r = Complex.I^j*Complex.I^(r-j) := by rw [← pow_add,Nat.add_sub_of_le hjle]
  rw [hI,show -(Complex.I/2)=(-1/2:ℂ)*Complex.I by ring]
  simp only [mul_pow,div_eq_mul_inv,mul_inv_rev]
  ring

end
end CarryC3Gamma
