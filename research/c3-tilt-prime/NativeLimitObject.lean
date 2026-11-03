import HankelLimitObject
import SourceNative

/-!
# O objeto-limite da fonte nativa: fechando o círculo

Instancia o objeto-limite (`HankelLimitObject`) na **fonte nativa** `nativeH` e liga sua
positividade-limite à torre consistente da leitura de Bézout nativa — amarrando o objeto
abstrato à fonte específica do operador.

* `native_limit_nonneg_iff_tower`: a positividade do objeto-limite nativo é exatamente a
  torre das câmeras de momentos nativas (instância incondicional do teorema geral).
* `native_hankel_posSemidef_iff_bezout`: em cada ordem, a câmera de momentos nativa e a
  câmera de Bézout nativa têm a mesma positividade (congruência pela transição nativa, que
  é invertível porque `nativeC 0 ≥ 1/3 > 0`).
* `native_limit_nonneg_iff_bezout_tower`: **o círculo fechado** — a positividade do
  objeto-limite da leitura nativa é exatamente a torre consistente da leitura de Bézout
  nativa.

Matriz e sinal, fonte específica; nada de zeros, nada de RH. Não modifica nada existente.
-/

namespace CarryTiltSlice
open CarrySourceBezout
open scoped Matrix
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- O termo constante da fonte nativa é positivo (`nativeC 0 ≥ 1/3`). -/
theorem nativeC_zero_pos : 0 < nativeC 0 :=
  lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 3)
    CarrySelfAdjointOperator.completedNativeRealEvenCharacteristicCoefficient_zero_ge_third

/-- Congruência preserva (e reflete) a positividade **semidefinida**. -/
theorem posSemidef_congr_transpose_iff {r : ℕ} (U M : Matrix (Fin r) (Fin r) ℝ) (hU : IsUnit U) :
    (U * M * Uᵀ).PosSemidef ↔ M.PosSemidef := by
  have hstar : (Uᵀ : Matrix (Fin r) (Fin r) ℝ) = star U := by
    ext i j
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, Matrix.transpose_apply,
      star_trivial]
  rw [hstar]
  exact Matrix.IsUnit.posSemidef_star_right_conjugate_iff hU

/-- **Instância nativa do objeto-limite.** A positividade do objeto-limite nativo é
exatamente a torre das câmeras de momentos nativas. -/
theorem native_limit_nonneg_iff_tower (s : ℕ) :
    (∀ x : ℕ →₀ ℝ, 0 ≤ hankelForm nativeH s x) ↔
      (∀ r, (hankelMatrix nativeH s r).PosSemidef) :=
  hankelForm_nonneg_iff_tower nativeH s

/-- Em cada ordem, a câmera de momentos nativa e a câmera de Bézout nativa têm a mesma
positividade semidefinida. -/
theorem native_hankel_posSemidef_iff_bezout (b : Bool) (r : ℕ) :
    (hankelMatrix nativeH (if b then 1 else 0) r).PosSemidef ↔
      (coefficientBlock (sourceKernel nativeC b) r).PosSemidef := by
  rw [source_bezout_to_hankel_congruence nativeC nativeH native_source_recurrence]
  exact (posSemidef_congr_transpose_iff _ _
    (isUnit_convolutionMatrix nativeC r nativeC_zero_pos.ne')).symm

/-- **O círculo fechado.** A positividade do objeto-limite da leitura nativa é exatamente a
torre consistente da leitura de Bézout nativa. -/
theorem native_limit_nonneg_iff_bezout_tower (b : Bool) :
    (∀ x : ℕ →₀ ℝ, 0 ≤ hankelForm nativeH (if b then 1 else 0) x) ↔
      (∀ r, (coefficientBlock (sourceKernel nativeC b) r).PosSemidef) := by
  rw [hankelForm_nonneg_iff_tower]
  exact forall_congr' fun r => native_hankel_posSemidef_iff_bezout b r

#print axioms nativeC_zero_pos
#print axioms native_hankel_posSemidef_iff_bezout
#print axioms native_limit_nonneg_iff_bezout_tower

end
end CarryTiltSlice
