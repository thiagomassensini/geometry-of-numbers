import LogOperatorBridge
import CarrySelfAdjointOperator.NativeLogEvolution

/-!
# Ponte com o operador autoadjunto real `nativeLogGenerator`

Liga os objetos do tilt ao gerador logarítmico **genuíno** do repositório do operador
(`nativeLogGenerator`, autoadjunto em `ℓ²(ℕ,ℂ)`, com `L e_n = log(n+1) e_n`), em vez de
funções explícitas:

* `logEigenvalue n = infiniteRealSpectralFrequency n` (a frequência que eu usei é a do operador);
* a frequência da célula C3 `k` é o **autovalor genuíno** de `nativeLogGenerator` no vetor
  de base `e_{3k+2}` (coordenada `c_k − 1`);
* a diagonal `logSqDiagonal` da curvatura é o quadrado da frequência do operador.

Honestidade: isto usa o operador real e seus teoremas (`nativeLogGenerator_basisVector_log`,
autoadjunticidade). Ainda **não** constrói `‖L^m v‖²` como norma da `m`-ésima potência não
limitada de `L` sobre a soma infinita `v = Σ √w_k e_{c_k−1}` (iteração de `LinearPMap` +
domínios) — essa é a etapa restante; aqui fica provado que as frequências/curvatura são
exatamente os dados espectrais do operador autoadjunto genuíno.

Não modifica nenhum módulo anterior.
-/

namespace CarryTiltSlice
open CPFormal.Analytic.Cp CarrySelfAdjointOperator
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- A frequência que eu defini é exatamente a do gerador real. -/
theorem logEigenvalue_eq_nativeFrequency (n : ℕ) :
    logEigenvalue n = infiniteRealSpectralFrequency n := by
  simp only [logEigenvalue, infiniteRealSpectralFrequency, Nat.cast_add, Nat.cast_one]

/-- A frequência da célula C3 `k` é a frequência do operador na coordenada `c_k − 1 = 3k+2`. -/
theorem center_log_eq_nativeFrequency (k : ℕ) :
    Real.log (canonicalRealCpCenter k) = infiniteRealSpectralFrequency (3 * k + 2) := by
  rw [center_log_eq_logEigenvalue, logEigenvalue_eq_nativeFrequency]

/-- A frequência da célula é um **autovalor genuíno** do operador autoadjunto real:
`nativeLogGenerator e_{3k+2} = (log c_k) • e_{3k+2}`. -/
theorem nativeLogGenerator_cell_eigenvalue (k : ℕ) :
    nativeLogGenerator
        ⟨infiniteRealSpectralBasisVector (3 * k + 2),
          nativeLogBasisVector_mem_domain (3 * k + 2)⟩ =
      (Real.log (canonicalRealCpCenter k) : ℂ) •
        infiniteRealSpectralBasisVector (3 * k + 2) := by
  rw [nativeLogGenerator_basisVector_log]
  congr 2
  unfold canonicalRealCpCenter
  push_cast
  ring

/-- A diagonal de `L²` usada na curvatura é o quadrado da frequência do operador real. -/
theorem logSqDiagonal_eq_nativeFrequencySq (j : ℕ) :
    logSqDiagonal j = (infiniteRealSpectralFrequency j) ^ 2 := by
  rw [logSqDiagonal, logEigenvalue_eq_nativeFrequency]

/-- Consequência: a curvatura por célula do tilt é a segunda diferença posicional das
frequências-ao-quadrado do operador autoadjunto genuíno. -/
theorem cpTiltThreeSecondDeriv_eq_nativeFrequencySq_secondDiff (k : ℕ) :
    cpTiltThreeSecondDeriv (canonicalRealCpCenter k) 0 =
      (infiniteRealSpectralFrequency (3 * (k + 1) - 2)) ^ 2 -
        2 * (infiniteRealSpectralFrequency (3 * (k + 1) - 1)) ^ 2 +
          (infiniteRealSpectralFrequency (3 * (k + 1))) ^ 2 := by
  rw [cpTiltThreeSecondDeriv_eq_logSq_secondDiff, logSqDiagonal_eq_nativeFrequencySq,
    logSqDiagonal_eq_nativeFrequencySq, logSqDiagonal_eq_nativeFrequencySq]

#print axioms center_log_eq_nativeFrequency
#print axioms nativeLogGenerator_cell_eigenvalue
#print axioms cpTiltThreeSecondDeriv_eq_nativeFrequencySq_secondDiff

end
end CarryTiltSlice
