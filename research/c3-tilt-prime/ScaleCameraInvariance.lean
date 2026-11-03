import SourceBezout
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real

/-!
# Invariância de escala/câmera do sinal (matriz e sinal, não localização de zeros)

O ponto é intrínseco: a positividade da leitura espectral é um **invariante de
congruência** — não depende da escolha de câmera (coordenada). O operador auto-adjunto
lê o espectro ortogonalmente; a leitura dos momentos (Hankel) é a *mesma leitura em outra
câmera*, ligada pela transição triangular `T = convolutionMatrix` via
`source_bezout_to_hankel_congruence`: `B = T · H · Tᵀ`.

Como `T` é invertível (quando `c₀ ≠ 0`), congruência preserva positividade, logo:

* **o sinal é independente da câmera** — `native_posDef_camera_invariant`,
  `native_det_sign_camera_invariant`;
* **o sinal é invariante por mudança de escala geométrica** `h_n ↦ C·Bⁿ·h_n` (a lei de
  escala cuja compatibilidade entre escalas é o conteúdo da teoria) —
  `hankel_rescale_posDef_iff`.

Isto formaliza "o que não muda quando tudo muda": positividade é propriedade do estado,
não da base. Não fala de zeros, não assume RH, não depende de localização. Módulo novo,
auto-contido (só Mathlib + `SourceBezout`).
-/

namespace CarryTiltSlice
open CarrySourceBezout
open scoped Matrix
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Núcleo: positividade é invariante de congruência -/

/-- **O sinal não é artefato de coordenada.** Para `U` invertível (sobre `ℝ`),
`U · M · Uᵀ` é positivo definido se e só se `M` é. -/
theorem posDef_congr_transpose_iff {r : ℕ} (U M : Matrix (Fin r) (Fin r) ℝ) (hU : IsUnit U) :
    (U * M * Uᵀ).PosDef ↔ M.PosDef := by
  have hstar : (Uᵀ : Matrix (Fin r) (Fin r) ℝ) = star U := by
    ext i j
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, Matrix.transpose_apply,
      star_trivial]
  rw [hstar]
  exact Matrix.IsUnit.posDef_star_right_conjugate_iff hU

/-- Escalar positivo preserva (e reflete) positividade definida. -/
theorem smul_posDef_iff {r : ℕ} {a : ℝ} (ha : 0 < a) (M : Matrix (Fin r) (Fin r) ℝ) :
    (a • M).PosDef ↔ M.PosDef := by
  refine ⟨fun h => ?_, fun h => h.smul ha⟩
  have h2 := h.smul (a := a⁻¹) (inv_pos.mpr ha)
  rwa [smul_smul, inv_mul_cancel₀ ha.ne', one_smul] at h2

/-! ## Câmera: a transição triangular preserva o sinal -/

/-- A transição de câmera (convolução triangular) é invertível quando `c₀ ≠ 0`. -/
theorem isUnit_convolutionMatrix (c : ℕ → ℝ) (r : ℕ) (hc : c 0 ≠ 0) :
    IsUnit (convolutionMatrix c r) := by
  rw [Matrix.isUnit_iff_isUnit_det, convolutionMatrix_det]
  exact (isUnit_iff_ne_zero.mpr hc).pow r

/-- **O sinal é independente da câmera.** A leitura de Bézout e a leitura dos momentos
(Hankel) têm exatamente a mesma positividade — ligadas pela transição `T`. -/
theorem native_posDef_camera_invariant (c h : ℕ → ℝ) (hc : SourceRecurrence c h)
    (hc0 : c 0 ≠ 0) (b : Bool) (r : ℕ) :
    (coefficientBlock (sourceKernel c b) r).PosDef ↔
      (hankelMatrix h (if b then 1 else 0) r).PosDef := by
  rw [source_bezout_to_hankel_congruence c h hc]
  exact posDef_congr_transpose_iff _ _ (isUnit_convolutionMatrix c r hc0)

/-- O sinal do determinante da leitura é invariante da câmera (fator `c₀^{2r} > 0`). -/
theorem native_det_sign_camera_invariant (c h : ℕ → ℝ) (hc : SourceRecurrence c h)
    (hc0 : c 0 ≠ 0) (b : Bool) (r : ℕ) :
    0 < (coefficientBlock (sourceKernel c b) r).det ↔
      0 < (hankelMatrix h (if b then 1 else 0) r).det := by
  have hc0r : c 0 ^ r ≠ 0 := pow_ne_zero r hc0
  have hpos : 0 < c 0 ^ (2 * r) := by
    have h2 : c 0 ^ (2 * r) = (c 0 ^ r) ^ 2 := by rw [← pow_mul, Nat.mul_comm]
    rw [h2]; positivity
  rw [source_bezout_det c h hc, mul_pos_iff_of_pos_left hpos]

/-! ## Escala: a lei de escala geométrica preserva o sinal -/

/-- Reescalonamento geométrico da sequência: `h_n ↦ C·Bⁿ·h_n` (mudança de escala/câmera). -/
def rescaleSeq (C B : ℝ) (h : ℕ → ℝ) : ℕ → ℝ := fun n => C * B ^ n * h n

/-- O Hankel reescalado é uma **congruência diagonal** (vezes escalar) do Hankel original:
a mudança de escala atua por conjugação, não altera o tipo de forma. -/
theorem hankelMatrix_rescale (C B : ℝ) (h : ℕ → ℝ) (s r : ℕ) :
    hankelMatrix (rescaleSeq C B h) s r =
      (C * B ^ s) • (Matrix.diagonal (fun i : Fin r => B ^ i.val)
        * hankelMatrix h s r * Matrix.diagonal (fun i : Fin r => B ^ i.val)) := by
  ext i j
  simp only [hankelMatrix, rescaleSeq, Matrix.smul_apply, smul_eq_mul,
    Matrix.diagonal_mul, Matrix.mul_diagonal]
  have hpow : B ^ (i.val + j.val + s) = B ^ s * B ^ i.val * B ^ j.val := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  rw [hpow]; ring

/-- **O sinal é invariante por mudança de escala geométrica.** Para `C, B > 0`, o Hankel
reescalado é positivo definido se e só se o original é. A escolha de escala/câmera não
muda a leitura do sinal. -/
theorem hankel_rescale_posDef_iff (C B : ℝ) (hC : 0 < C) (hB : 0 < B) (h : ℕ → ℝ) (s r : ℕ) :
    (hankelMatrix (rescaleSeq C B h) s r).PosDef ↔ (hankelMatrix h s r).PosDef := by
  have hDunit : IsUnit (Matrix.diagonal (fun i : Fin r => B ^ i.val)) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_diagonal]
    exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ hB.ne')
  have hsymm : (Matrix.diagonal (fun i : Fin r => B ^ i.val))ᵀ
      = Matrix.diagonal (fun i : Fin r => B ^ i.val) := Matrix.diagonal_transpose _
  rw [hankelMatrix_rescale, smul_posDef_iff (mul_pos hC (pow_pos hB s))]
  calc
    (Matrix.diagonal (fun i : Fin r => B ^ i.val) * hankelMatrix h s r
          * Matrix.diagonal (fun i : Fin r => B ^ i.val)).PosDef
        ↔ (Matrix.diagonal (fun i : Fin r => B ^ i.val) * hankelMatrix h s r
          * (Matrix.diagonal (fun i : Fin r => B ^ i.val))ᵀ).PosDef := by rw [hsymm]
    _ ↔ (hankelMatrix h s r).PosDef := posDef_congr_transpose_iff _ _ hDunit

#print axioms posDef_congr_transpose_iff
#print axioms native_posDef_camera_invariant
#print axioms native_det_sign_camera_invariant
#print axioms hankel_rescale_posDef_iff

end
end CarryTiltSlice
