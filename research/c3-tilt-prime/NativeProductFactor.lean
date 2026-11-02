import BezoutSourceProduct
import LiteralBudgetLimit
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Fatoração formal dos jets literais TFVD, com a cauda original

A cabeça e a cauda são os jets pares literais depois da síntese TFVD
preexistente. Seu quociente é um artifício algébrico sobre séries de jets,
não um novo estado ou um quociente de sinais físicos ponto a ponto.
-/
namespace CarrySourceBezout
open CarrySelfAdjointOperator NativeTrace Filter Matrix
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000

/-- O fator corretivo formal conserva exatamente a cauda literal. -/
def literalCorrectionSeries (M : ℕ) : PowerSeries ℂ :=
  1 + (sourceSeries (literalHead M))⁻¹ * sourceSeries (literalTail M)

def literalCorrection (M : ℕ) (n : ℕ) : ℂ :=
  PowerSeries.coeff n (literalCorrectionSeries M)

theorem literalCorrection_series (M : ℕ) :
    sourceSeries (literalCorrection M) = literalCorrectionSeries M := by
  apply PowerSeries.ext
  intro n
  simp [sourceSeries, literalCorrection]

theorem literal_head_constant_eventually_ne :
    ∀ᶠ M : ℕ in atTop, literalHead M 0 ≠ 0 := by
  have h : (nativeC 0 : ℂ) ≠ 0 := by
    exact_mod_cast completedNativeRealEvenCharacteristicCoefficient_zero_ne_zero
  exact (literal_head_tendsto 0).eventually_ne h

theorem literal_product_series (M : ℕ) (hM : literalHead M 0 ≠ 0) :
    sourceSeries (literalHead M) * literalCorrectionSeries M =
      sourceSeries (fun n => (nativeC n : ℂ)) := by
  have h0 : PowerSeries.constantCoeff (sourceSeries (literalHead M)) ≠ 0 := by
    simpa [sourceSeries, ← PowerSeries.coeff_zero_eq_constantCoeff_apply] using hM
  have hi := PowerSeries.mul_inv_cancel (sourceSeries (literalHead M)) h0
  have hsum : sourceSeries (fun n => (nativeC n : ℂ)) =
      sourceSeries (literalHead M) + sourceSeries (literalTail M) := by
    rw [literal_head_tail M, sourceSeries_add]
  rw [hsum]
  unfold literalCorrectionSeries
  calc
    _ = sourceSeries (literalHead M) +
        (sourceSeries (literalHead M) * (sourceSeries (literalHead M))⁻¹) *
          sourceSeries (literalTail M) := by ring
    _ = _ := by rw [hi]; simp

theorem literal_product_coefficients (M : ℕ) (hM : literalHead M 0 ≠ 0) :
    sourceProduct (literalHead M) (literalCorrection M) = fun n => (nativeC n : ℂ) := by
  funext n
  unfold sourceProduct
  rw [literalCorrection_series, literal_product_series M hM]
  simp [sourceSeries]

theorem literalCorrection_zero (M : ℕ) :
    literalCorrection M 0 = 1 + (literalHead M 0)⁻¹ * literalTail M 0 := by
  unfold literalCorrection literalCorrectionSeries
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp only [map_add, map_one, map_mul, PowerSeries.constantCoeff_inv]
  have hh : PowerSeries.constantCoeff (sourceSeries (literalHead M)) = literalHead M 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp [sourceSeries]
  have ht : PowerSeries.constantCoeff (sourceSeries (literalTail M)) = literalTail M 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp [sourceSeries]
  rw [hh, ht]

theorem literalCorrection_zero_tendsto_one :
    Tendsto (fun M => literalCorrection M 0) atTop (nhds 1) := by
  have h : (nativeC 0 : ℂ) ≠ 0 := by
    exact_mod_cast completedNativeRealEvenCharacteristicCoefficient_zero_ne_zero
  simp_rw [literalCorrection_zero]
  have hh := (literal_head_tendsto 0).inv₀ h
  have ht := literal_tail_tendsto_zero 0
  simpa using (tendsto_const_nhds.add (hh.mul ht))

theorem literalCorrection_constant_ne (M : ℕ) (hM : literalHead M 0 ≠ 0) :
    literalCorrection M 0 ≠ 0 := by
  have hp := congrFun (literal_product_coefficients M hM) 0
  have he : literalHead M 0 * literalCorrection M 0 = (nativeC 0 : ℂ) := by
    simpa [sourceProduct, sourceSeries, PowerSeries.coeff_mul] using hp
  have hn : (nativeC 0 : ℂ) ≠ 0 := by
    exact_mod_cast completedNativeRealEvenCharacteristicCoefficient_zero_ne_zero
  intro hzero
  rw [hzero, mul_zero] at he
  exact hn he.symm

#print axioms literal_head_constant_eventually_ne
#print axioms literal_product_coefficients
#print axioms literalCorrection_zero_tendsto_one
#print axioms literalCorrection_constant_ne
end
end CarrySourceBezout
