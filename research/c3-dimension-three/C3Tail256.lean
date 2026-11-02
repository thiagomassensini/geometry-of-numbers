import C3OrderRate
import CarrySelfAdjointOperator.CompletedNativeAllOrderMomentUpperBound

namespace CarryC3DimensionThree
open CarryUniformSource CarrySourceBezout CarrySelfAdjointOperator CPFormal.Analytic.Cp
open Filter Topology
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option backward.isDefEq.respectTransparency false

/-- The boundary is exactly the original PR70 boundary, at a specified cutoff. -/
def c3Head (M : ℕ) : ℕ → ℂ := repHead M (originalBoundaryJet M)
def c3Tail (M : ℕ) : ℕ → ℂ := repTail M (originalBoundaryJet M)

theorem c3Tail_jet (M k : ℕ) :
    c3Tail M k = NativeTrace.sourceJet (2*k)
      (fun w => NativeTrace.valueMultiplier w * CarryC3Tail.acceleratedC3Tail M w) := by
  unfold c3Tail repTail
  simp only [Pi.sub_apply,literalTail,originalBoundaryJet]
  have hsub := iteratedDeriv_sub (n:=2*k)
    (NativeTrace.tail_value_analytic M).contDiffAt (original_boundary_analytic M).contDiffAt
  simp only [NativeTrace.sourceJet]
  rw [← sub_div,← hsub]
  congr 1
  congr 1
  funext w
  dsimp only [Pi.sub_apply]
  rw [literal_tail_value_formula]
  unfold CarryC3Tail.acceleratedC3Tail
  ring

theorem c3Tail_original_bound (M k : ℕ) (hM : 0 < M) :
    ‖c3Tail M k‖ ≤ (96*(Nat.factorial 14:ℝ)/(729*(3*(M:ℝ)-1)^13))*4^(2*k) := by
  rw [c3Tail_jet]
  apply CarryC3Tail.cauchy_quarter
  · intro w hw
    exact (CarryC3Tail.value_multiplier_analytic_at w (lt_of_le_of_lt hw (by norm_num))).mul
      (CarryC3Tail.accelerated_c3_tail_analytic M w (lt_of_le_of_lt hw (by norm_num)))
  · intro w hw
    rw [norm_mul]
    have htail := CarryC3Tail.accelerated_c3_tail_bound M hM w (hw.trans (by norm_num))
    have hmult := CarryC3Tail.c3_value_multiplier_bound w hw
    have hb := mul_le_mul hmult htail (norm_nonneg _) (by norm_num : (0:ℝ)≤96)
    exact hb.trans_eq (by ring)

theorem c3Tail256_six_bound (k : ℕ) (hk : k ≤ 6) :
    ‖c3Tail 256 k‖ ≤ (1/10^20:ℝ) := by
  have h := c3Tail_original_bound 256 k (by norm_num)
  have hp : (4:ℝ)^(2*k) ≤ (4:ℝ)^12 := by
    gcongr
    · norm_num
    · omega
  apply h.trans
  norm_num at hp ⊢
  nlinarith

/-- The zeroth coefficient uses the existing C3 box; all higher absolute
bounds use the known theta representation without assuming Hankel signs. -/
theorem native_source_coeff_abs_half (k : ℕ) : |nativeC k| ≤ (1/2:ℝ) := by
  cases k with
  | zero =>
    have hb := native_four_reference_bounds ⟨0,by norm_num⟩
    have hreal := (Complex.abs_re_le_norm ((nativeC 0:ℂ)-twoEvenReference 0)).trans hb
    have h0 : |nativeC 0 - (497120778188314/1000000000000000:ℝ)| ≤ (1/10^12:ℝ) := by
      simpa [twoEvenReference,twoEvenReferenceReal] using hreal
    have hh := abs_le.mp h0
    rw [abs_le]
    constructor <;> linarith
  | succ n =>
    have hb := completedNativeRealEvenCharacteristicCoefficient_succ_abs_upper n
    change |nativeC (n+1)| ≤ (1/(35*25^n):ℝ) at hb
    have hp : (1:ℝ) ≤ 25^n := one_le_pow₀ (by norm_num)
    have hdiv : (1/(35*25^n):ℝ) ≤ 1/35 := by
      apply (div_le_div_iff₀ (by positivity) (by norm_num)).2
      nlinarith
    linarith

theorem c3_source_split (M k : ℕ) : c3Head M k + c3Tail M k = (nativeC k:ℂ) := by
  have hh := congrFun (literal_head_tail M) k
  simp only [Pi.add_apply] at hh
  simp only [c3Head,c3Tail,repHead,repTail,Pi.add_apply,Pi.sub_apply]
  rw [hh]
  ring

theorem c3Head256_six_bound (k : ℕ) (hk : k ≤ 6) : ‖c3Head 256 k‖ ≤ (1:ℝ) := by
  have he : c3Head 256 k = (nativeC k:ℂ)-c3Tail 256 k := by
    have hh := c3_source_split 256 k
    linear_combination hh
  rw [he]
  have hh := norm_sub_le (nativeC k:ℂ) (c3Tail 256 k)
  have hc := native_source_coeff_abs_half k
  have ht := c3Tail256_six_bound k hk
  simp only [Complex.norm_real,Real.norm_eq_abs] at hh
  linarith

#print axioms native_source_coeff_abs_half
#print axioms c3Head256_six_bound

#print axioms c3Tail_original_bound
#print axioms c3Tail256_six_bound
end
end CarryC3DimensionThree
