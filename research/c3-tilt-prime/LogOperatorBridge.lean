import CriticalCurvature

/-!
# Ponte com o gerador autoadjunto logarítmico `L`

Interpreta os objetos do tilt como dados espectrais do gerador logarítmico original
`L` (com `L e_n = log(n+1) e_n`, cf. `nativeLogGenerator_basisVector_log`):

1. **Jets pares = normas quadráticas.** Com `v = Σ_k √w_k e_{c_k−1}` no espaço diagonal,
   `(-1)^m G^{(2m)}(0) = Σ_k w_k (log c_k)^{2m} = ‖L^m v‖²` (soma de quadrados ℓ²),
   estritamente positiva e finita em cada ordem `m`.
2. **Curvatura = segunda diferença da diagonal de `L²`.** A curvatura por célula
   `Δ₁(log x)²(c_k)` é a segunda diferença posicional de `q_j = ⟨e_j, L² e_j⟩ = (log(j+1))²`
   nos endereços `c_k−2, c_k−1, c_k`.

Honestidade: isto realiza os **autovalores** de `L` como funções explícitas e prova as
identidades; NÃO importa o operador nem seus espaços/domínios/transportes. A identificação
com o readout completo do operador transportado continua exigindo preservar espaços, estados
e mapas da construção original (cf. `greenStateMaterialLogGenerator_domain_iff_log_moment`).
Também não se confunde com a matriz de Jacobi que recupera as alturas `γ_j`.

Não modifica nenhum módulo anterior.
-/

namespace CarryTiltSlice
open CPFormal.Analytic.Cp CarrySelfAdjointOperator
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- Autovalor do gerador logarítmico `L` na coordenada `n` (`L e_n = log(n+1) e_n`). -/
def logEigenvalue (n : ℕ) : ℝ := Real.log (n + 1)

/-- A frequência da célula C3 `k` é o autovalor de `L` na coordenada `c_k − 1 = 3k+2`. -/
theorem center_log_eq_logEigenvalue (k : ℕ) :
    Real.log (canonicalRealCpCenter k) = logEigenvalue (3 * k + 2) := by
  unfold logEigenvalue canonicalRealCpCenter
  norm_num
  ring_nf

/-! ## 1. Jets pares do tilt como normas quadráticas de `L^m v` -/

/-- Componente `k` de `L^m v`, com `v = Σ_k √w_k e_{c_k−1}`: `(log c_k)^m · √w_k`. -/
def tiltSpectralVector (m k : ℕ) : ℝ :=
  (Real.log (canonicalRealCpCenter k)) ^ m * Real.sqrt (wCoeff k)

/-- O quadrado de cada componente é o termo do jato misto. -/
theorem tiltSpectralVector_sq (m k : ℕ) :
    (tiltSpectralVector m k) ^ 2 = mixedTiltTerm m k := by
  have hw : 0 ≤ wCoeff k := wCoeff_nonneg k
  unfold tiltSpectralVector
  rw [mul_pow, Real.sq_sqrt hw, ← pow_mul, mul_comm m 2]
  unfold mixedTiltTerm wCoeff
  exact mul_comm _ _

/-- **Jets pares do tilt = `‖L^m v‖²`** (soma de quadrados ℓ² no modelo diagonal). -/
theorem tilt_jet_eq_normSq (m : ℕ) :
    ((-1:ℂ) ^ m * iteratedDeriv (2 * m)
        (fun t : ℝ => infiniteMixedTiltResponse (t:ℂ)) 0).re
      = ∑' k : ℕ, (tiltSpectralVector m k) ^ 2 := by
  rw [infinite_mixed_tilt_identity]
  exact tsum_congr (fun k => (tiltSpectralVector_sq m k).symm)

/-- A norma quadrática é finita em cada ordem (`L^m v ∈ ℓ²`). -/
theorem tiltSpectralVector_sq_summable (m : ℕ) :
    Summable (fun k : ℕ => (tiltSpectralVector m k) ^ 2) := by
  have h : (fun k : ℕ => (tiltSpectralVector m k) ^ 2) = mixedTiltTerm m :=
    funext (tiltSpectralVector_sq m)
  rw [h]; exact mixedTiltTerm_summable m

/-- A norma quadrática é estritamente positiva em cada ordem. -/
theorem tilt_jet_normSq_pos (m : ℕ) :
    0 < ∑' k : ℕ, (tiltSpectralVector m k) ^ 2 := by
  have h : (fun k : ℕ => (tiltSpectralVector m k) ^ 2) = mixedTiltTerm m :=
    funext (tiltSpectralVector_sq m)
  rw [h]; exact mixedTiltTerm_tsum_pos m

#print axioms tilt_jet_eq_normSq
#print axioms tilt_jet_normSq_pos

/-! ## 2. Curvatura por célula = segunda diferença da diagonal de `L²` -/

/-- Diagonal de `L²`: `⟨e_j, L² e_j⟩ = (log(j+1))²`. -/
def logSqDiagonal (j : ℕ) : ℝ := (logEigenvalue j) ^ 2

/-- A curvatura por célula do tilt é a segunda diferença posicional da diagonal de `L²`
nos endereços `c_k − 2, c_k − 1, c_k` (centros canônicos `c_k = 3(k+1)`). -/
theorem cpTiltThreeSecondDeriv_eq_logSq_secondDiff (k : ℕ) :
    cpTiltThreeSecondDeriv (canonicalRealCpCenter k) 0 =
      logSqDiagonal (3 * (k + 1) - 2) - 2 * logSqDiagonal (3 * (k + 1) - 1) +
        logSqDiagonal (3 * (k + 1)) := by
  rw [cpTiltThreeSecondDeriv_zero]
  have h2 : (2:ℕ) ≤ 3 * (k + 1) := by omega
  have h1 : (1:ℕ) ≤ 3 * (k + 1) := by omega
  have ha : ((3 * (k + 1) - 2 : ℕ) : ℝ) + 1 = canonicalRealCpCenter k - 1 := by
    rw [Nat.cast_sub h2]; unfold canonicalRealCpCenter; push_cast; ring
  have hb : ((3 * (k + 1) - 1 : ℕ) : ℝ) + 1 = canonicalRealCpCenter k := by
    rw [Nat.cast_sub h1]; unfold canonicalRealCpCenter; push_cast; ring
  have hc : ((3 * (k + 1) : ℕ) : ℝ) + 1 = canonicalRealCpCenter k + 1 := by
    unfold canonicalRealCpCenter; push_cast; ring
  simp only [logSqDiagonal, logEigenvalue, ha, hb, hc]
  ring

#print axioms cpTiltThreeSecondDeriv_eq_logSq_secondDiff

end
end CarryTiltSlice
