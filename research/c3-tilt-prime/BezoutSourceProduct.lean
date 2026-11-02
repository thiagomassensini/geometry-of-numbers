import SourceBezout

/-!
# Regra de produto para o kernel de Bézout da fonte

Identidade puramente algébrica em séries formais, nos dois setores e em
qualquer ordem. O transporte triangular dos blocos conserva ambas as parcelas.
Nenhuma hipótese de positividade ou identificação física é introduzida.
-/

namespace CarrySourceBezout
noncomputable section
variable {R : Type*} [CommRing R] [IsDomain R]

theorem bezout_leibniz_product (a c b d : PowerSeries R) :
    bezout (a*d+c*b) (c*d) =
      left d * right d * bezout a c + left c * right c * bezout b d := by
  apply mul_left_cancel₀ uv_ne_zero
  calc
    uv * bezout (a*d+c*b) (c*d) =
        left (a*d+c*b) * right (c*d) - right (a*d+c*b) * left (c*d) :=
      bezout_numerator _ _
    _ = left d * right d * (uv * bezout a c) +
        left c * right c * (uv * bezout b d) := by
      rw [bezout_numerator, bezout_numerator]
      simp only [map_add, map_mul]
      ring
    _ = uv * (left d * right d * bezout a c + left c * right c * bezout b d) := by ring

def bezoutFromSeries (c : PowerSeries R) (shifted : Bool) : BiSeries R :=
  bezout (if shifted then -(PowerSeries.derivative R c)
    else PowerSeries.X * -(PowerSeries.derivative R c)) c

theorem bezoutFromSeries_mul (c d : PowerSeries R) (shifted : Bool) :
    bezoutFromSeries (c*d) shifted =
      left d * right d * bezoutFromSeries c shifted +
      left c * right c * bezoutFromSeries d shifted := by
  have hder : (PowerSeries.derivative R) (c*d) =
      (PowerSeries.derivative R) c * d + c * (PowerSeries.derivative R) d := by
    change PowerSeries.derivativeFun (c*d) =
      PowerSeries.derivativeFun c * d + c * PowerSeries.derivativeFun d
    rw [PowerSeries.derivativeFun_mul]
    simp only [smul_eq_mul]
    ring
  cases shifted
  · simp only [bezoutFromSeries, Bool.false_eq_true, ↓reduceIte]
    have he : PowerSeries.X * -((PowerSeries.derivative R) (c*d)) =
        (PowerSeries.X * -(PowerSeries.derivative R c))*d +
          c*(PowerSeries.X * -(PowerSeries.derivative R d)) := by
      rw [hder]; ring
    rw [he]
    exact bezout_leibniz_product _ _ _ _
  · simp only [bezoutFromSeries, ↓reduceIte]
    have he : -((PowerSeries.derivative R) (c*d)) =
        (-(PowerSeries.derivative R c))*d + c*(-(PowerSeries.derivative R d)) := by
      rw [hder]; ring
    rw [he]
    exact bezout_leibniz_product _ _ _ _

/-- Coefficients of the product of the original source series. -/
def sourceProduct (c d : ℕ → R) : ℕ → R :=
  fun n => PowerSeries.coeff n (sourceSeries c * sourceSeries d)

omit [IsDomain R] in
theorem sourceSeries_sourceProduct (c d : ℕ → R) :
    sourceSeries (sourceProduct c d) = sourceSeries c * sourceSeries d := by
  apply PowerSeries.ext
  intro n
  simp [sourceSeries, sourceProduct]

theorem sourceKernel_product (c d : ℕ → R) (shifted : Bool) :
    sourceKernel (sourceProduct c d) shifted =
      left (sourceSeries d) * right (sourceSeries d) * sourceKernel c shifted +
      left (sourceSeries c) * right (sourceSeries c) * sourceKernel d shifted := by
  have he (x : ℕ → R) : sourceKernel x shifted = bezoutFromSeries (sourceSeries x) shifted := by
    cases shifted <;> simp [sourceKernel, bezoutFromSeries]
  rw [he, he, he, sourceSeries_sourceProduct]
  exact bezoutFromSeries_mul (sourceSeries c) (sourceSeries d) shifted

omit [IsDomain R] in
/-- Exact triangular transport of an arbitrary two-variable kernel. -/
theorem coefficient_transport (c : ℕ → R) (f : BiSeries R) (r : ℕ) :
    coefficientBlock (left (sourceSeries c) * right (sourceSeries c) * f) r =
      convolutionMatrix c r * coefficientBlock f r * (convolutionMatrix c r).transpose := by
  ext i j
  rw [show left (sourceSeries c) * right (sourceSeries c) * f =
      left (sourceSeries c) * (right (sourceSeries c) * f) by ring]
  change PowerSeries.coeff j.val (PowerSeries.coeff i.val
    (left (sourceSeries c) * (right (sourceSeries c) * f))) = _
  rw [coeff_product_finite _ _ r i]
  simp only [left, PowerSeries.coeff_map, sourceSeries, PowerSeries.coeff_mk]
  simp only [map_sum, ite_mul, apply_ite, PowerSeries.coeff_C_mul, zero_mul, map_zero]
  change (∑ a : Fin r, (if a.val ≤ i.val then
      c (i.val-a.val) * PowerSeries.coeff j.val (PowerSeries.coeff a.val
        (right (sourceSeries c) * f)) else 0)) = _
  simp only [Matrix.mul_apply, Matrix.transpose_apply, convolutionMatrix, coefficientBlock]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hai : a.val ≤ i.val
  · simp only [hai, ↓reduceIte]
    simp only [right, PowerSeries.coeff_C_mul]
    rw [coeff_product_finite _ _ r j]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    simp only [sourceSeries, PowerSeries.coeff_mk]
    ring
  · simp [hai]

/-- Finite blocks retain both product contributions and all their crossings. -/
theorem sourceKernel_product_block (c d : ℕ → R) (shifted : Bool) (r : ℕ) :
    coefficientBlock (sourceKernel (sourceProduct c d) shifted) r =
      convolutionMatrix d r * coefficientBlock (sourceKernel c shifted) r *
          (convolutionMatrix d r).transpose +
      convolutionMatrix c r * coefficientBlock (sourceKernel d shifted) r *
          (convolutionMatrix c r).transpose := by
  rw [sourceKernel_product]
  have h_add : coefficientBlock
      (left (sourceSeries d) * right (sourceSeries d) * sourceKernel c shifted +
        left (sourceSeries c) * right (sourceSeries c) * sourceKernel d shifted) r =
      coefficientBlock (left (sourceSeries d) * right (sourceSeries d) * sourceKernel c shifted) r +
      coefficientBlock (left (sourceSeries c) * right (sourceSeries c) * sourceKernel d shifted) r := by
    ext i j
    simp [coefficientBlock]
  rw [h_add, coefficient_transport, coefficient_transport]

#print axioms bezout_leibniz_product
#print axioms bezoutFromSeries_mul
#print axioms sourceKernel_product
#print axioms sourceKernel_product_block
end
end CarrySourceBezout
