import SourceBoxes

/-! The quadrature weights are exactly rational on the existing grid.
This computes their exact value before the single outward rounding. -/
namespace CarryIntegralCertificate
open Real
set_option autoImplicit false
set_option maxHeartbeats 1200000

def rationalGridWeight (p r j : ℕ) : ℚ :=
  (∑ k ∈ Finset.range (p+1),
    (Nat.fast_choose p k:ℚ)*(j:ℚ)^(p-k)/(k+r+1))/64^(p+r+1)

theorem rationalGridWeight_eq (p r j : ℕ) :
    (rationalGridWeight p r j:ℝ) =
      weightedPowerMass p r ((j:ℝ)/64) (((j+1:ℕ):ℝ)/64) := by
  unfold rationalGridWeight weightedPowerMass
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  have hkp : k ≤ p := by have h := Finset.mem_range.mp hk; omega
  have he : p+r+1 = (p-k)+(k+r+1) := by omega
  have hb : ((j:ℝ)+1)/64-(j:ℝ)/64 = 1/64 := by ring
  rw [← Nat.choose_eq_fast_choose,hb,div_pow,div_pow,one_pow,he,pow_add]
  ring

theorem rationalGridWeight_nonneg (p r j : ℕ) : 0 ≤ rationalGridWeight p r j := by
  unfold rationalGridWeight
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro k _
    positivity
  · positivity

def exactGridWeightBox (p r j : ℕ) : Box := Box.ofRat (rationalGridWeight p r j)

theorem mem_exactGridWeightBox (p r j : ℕ) :
    (exactGridWeightBox p r j).Mem
      (weightedPowerMass p r ((j:ℝ)/64) (((j+1:ℕ):ℝ)/64)) := by
  rw [← rationalGridWeight_eq]
  exact mem_ofRat _

end CarryIntegralCertificate
