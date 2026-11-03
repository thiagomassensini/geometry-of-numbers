import HankelBilinearForm
import NativeLimitObject

/-!
# Cauchy–Schwarz na fonte nativa

Instancia o Cauchy–Schwarz do objeto-limite (`HankelBilinearForm`) na fonte nativa
`nativeH` e condiciona-o à torre consistente da leitura de Bézout nativa
(`NativeLimitObject`) — fechando o círculo também para a forma bilinear polarizada.

* `native_cauchy_schwarz`: se a torre de Bézout nativa é positiva semidefinida em toda
  ordem, então a forma bilinear polarizada nativa satisfaz Cauchy–Schwarz.

Matriz e sinal, forma bilinear, fonte nativa; nada de zeros, nada de RH. Só adiciona.
-/

namespace CarryTiltSlice
open CarrySourceBezout
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- **Cauchy–Schwarz da fonte nativa.** Se a torre de Bézout nativa é positiva
semidefinida em cada ordem, então a forma bilinear polarizada da leitura de momentos
nativa satisfaz a desigualdade de Cauchy–Schwarz. -/
theorem native_cauchy_schwarz (b : Bool)
    (htower : ∀ r, (coefficientBlock (sourceKernel nativeC b) r).PosSemidef)
    (x y : ℕ →₀ ℝ) :
    hankelBilin nativeH (if b then 1 else 0) x y ^ 2
      ≤ hankelForm nativeH (if b then 1 else 0) x
        * hankelForm nativeH (if b then 1 else 0) y :=
  hankelBilin_sq_le nativeH (if b then 1 else 0)
    ((native_limit_nonneg_iff_bezout_tower b).mpr htower) x y

#print axioms native_cauchy_schwarz

end
end CarryTiltSlice
