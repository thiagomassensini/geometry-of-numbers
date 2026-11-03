import ScaleCameraInvariance

/-!
# Coerência de câmera entre ordens (torre consistente → passagem ao limite)

A invariância de câmera (`ScaleCameraInvariance`) diz que, em cada ordem, o sinal não
depende da escolha de câmera. Falta o ingrediente para **passar ao limite sem duplicar
informação**: a leitura num corte finito é exatamente a *restrição* da leitura num corte
maior. Isto torna a família `{B_r}`, `{H_r}` e a transição `{T_r}` um **sistema projetivo
coerente** — a estrutura que permite falar do operador no limite.

* Coerência da transição/leituras: a submatriz pelo prefixo `Fin r ↪ Fin R` (`Fin.castLE`)
  de qualquer ordem maior reproduz exatamente a ordem menor
  (`convolutionMatrix_castLE`, `hankelMatrix_castLE`, `coefficientBlock_castLE`).
* **Torre consistente do sinal**: se a leitura é positiva numa ordem maior, é positiva em
  toda ordem menor (submatriz principal de PosDef é PosDef) —
  `hankel_posDef_mono`, `native_bezout_posDef_mono`.
* **Torre independente de câmera**: positividade em ordem maior na câmera de Bézout dá
  positividade da leitura de momentos em toda ordem menor — `native_reading_tower`.

Matriz e sinal, estrutura de restrição coerente; nada de zeros, nada de RH. Módulo novo,
não modifica nada existente.
-/

namespace CarryTiltSlice
open CarrySourceBezout
open scoped Matrix
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Coerência de prefixo: o sistema projetivo das leituras -/

/-- A transição de câmera é coerente entre ordens: o prefixo `Fin r` da ordem `R` é a
transição de ordem `r`. -/
theorem convolutionMatrix_castLE {c : ℕ → ℝ} {r R : ℕ} (hr : r ≤ R) :
    (convolutionMatrix c R).submatrix (Fin.castLE hr) (Fin.castLE hr) = convolutionMatrix c r := by
  ext i j
  simp [convolutionMatrix, Matrix.submatrix_apply]

/-- A leitura dos momentos (Hankel) é coerente entre ordens. -/
theorem hankelMatrix_castLE {h : ℕ → ℝ} {s r R : ℕ} (hr : r ≤ R) :
    (hankelMatrix h s R).submatrix (Fin.castLE hr) (Fin.castLE hr) = hankelMatrix h s r := by
  ext i j
  simp [hankelMatrix, Matrix.submatrix_apply]

/-- A leitura de Bézout é coerente entre ordens. -/
theorem coefficientBlock_castLE {f : BiSeries ℝ} {r R : ℕ} (hr : r ≤ R) :
    (coefficientBlock f R).submatrix (Fin.castLE hr) (Fin.castLE hr) = coefficientBlock f r := by
  ext i j
  simp [coefficientBlock, Matrix.submatrix_apply]

/-! ## Torre consistente: a positividade desce no sistema projetivo -/

/-- **A leitura positiva é uma torre consistente.** Se a Hankel é positiva definida numa
ordem maior, é positiva definida em toda ordem menor (submatriz principal de PosDef). -/
theorem hankel_posDef_mono {h : ℕ → ℝ} {s r R : ℕ} (hr : r ≤ R)
    (hpd : (hankelMatrix h s R).PosDef) : (hankelMatrix h s r).PosDef := by
  have hsub := hpd.submatrix (Fin.castLE_injective hr)
  rwa [hankelMatrix_castLE hr] at hsub

/-- Versão Bézout da torre consistente. -/
theorem native_bezout_posDef_mono {c : ℕ → ℝ} {b : Bool} {r R : ℕ} (hr : r ≤ R)
    (hpd : (coefficientBlock (sourceKernel c b) R).PosDef) :
    (coefficientBlock (sourceKernel c b) r).PosDef := by
  have hsub := hpd.submatrix (Fin.castLE_injective hr)
  rwa [coefficientBlock_castLE hr] at hsub

/-- **Torre consistente e independente de câmera.** Positividade da leitura de Bézout numa
ordem maior fornece positividade da leitura de momentos em toda ordem menor — a leitura
restringe coerentemente e o sinal não depende da câmera. Esta é a estrutura projetiva que
permite passar o operador ao limite. -/
theorem native_reading_tower (c h : ℕ → ℝ) (hc : SourceRecurrence c h) (hc0 : c 0 ≠ 0)
    (b : Bool) {r R : ℕ} (hr : r ≤ R)
    (hpd : (coefficientBlock (sourceKernel c b) R).PosDef) :
    (hankelMatrix h (if b then 1 else 0) r).PosDef :=
  (native_posDef_camera_invariant c h hc hc0 b r).mp (native_bezout_posDef_mono hr hpd)

#print axioms convolutionMatrix_castLE
#print axioms hankel_posDef_mono
#print axioms native_bezout_posDef_mono
#print axioms native_reading_tower

end
end CarryTiltSlice
