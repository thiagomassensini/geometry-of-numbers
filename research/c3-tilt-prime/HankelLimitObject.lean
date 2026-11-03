import CameraCoherence
import Mathlib.Data.Finsupp.Basic

/-!
# O objeto-limite explícito: a forma de Hankel em `ℕ →₀ ℝ`

A torre projetiva coerente `{hankelMatrix h s r}` (`CameraCoherence`) tem um **objeto-limite
explícito**: a forma quadrática na coordenada infinita finitamente suportada `ℕ →₀ ℝ`,

`hankelForm h s x = ∑_{i,j} x i · h(i+j+s) · x j`  (soma finita sobre o suporte).

Neste pin do Mathlib, `Matrix.PosSemidef` já é definido sobre vetores finitamente
suportados, então as câmeras finitas (`Fin r →₀ ℝ`) e o limite (`ℕ →₀ ℝ`) falam a mesma
língua, ligadas pela inclusão `embDomain : (Fin r →₀ ℝ) → (ℕ →₀ ℝ)`.

* `hankelForm_embDomain`: a forma-limite num vetor incluído da câmera `r` **é** a forma
  finita de `hankelMatrix h s r` — a leitura-limite restringe a cada câmera.
* `hankelForm_nonneg_iff_tower`: **a positividade do objeto-limite é exatamente a torre
  consistente de positividades finitas**:
  `(∀ x, 0 ≤ hankelForm h s x) ↔ ∀ r, (hankelMatrix h s r).PosSemidef`.

É a passagem ao limite: o sinal do operador no limite é o limite projetivo dos sinais das
câmeras. Matriz e sinal; nada de zeros, nada de RH. Auto-contido.
-/

namespace CarryTiltSlice
open CarrySourceBezout
open scoped Matrix BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- **Objeto-limite**: a forma quadrática de Hankel no vetor finitamente suportado `x`. -/
def hankelForm (h : ℕ → ℝ) (s : ℕ) (x : ℕ →₀ ℝ) : ℝ :=
  x.sum fun i xi => x.sum fun j xj => xi * h (i + j + s) * xj

/-- A matriz de Hankel é simétrica (Hermitiana sobre `ℝ`). -/
theorem hankelMatrix_isHermitian (h : ℕ → ℝ) (s r : ℕ) :
    (hankelMatrix h s r).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, hankelMatrix, star_trivial]
  congr 1
  omega

/-- **Coerência limite↔câmera.** A forma-limite num vetor incluído da câmera `r` coincide
com a forma finita de `hankelMatrix h s r`. -/
theorem hankelForm_embDomain (h : ℕ → ℝ) (s r : ℕ) (y : Fin r →₀ ℝ) :
    hankelForm h s (y.embDomain Fin.valEmbedding)
      = y.sum fun i yi => y.sum fun j yj => star yi * hankelMatrix h s r i j * yj := by
  unfold hankelForm
  rw [Finsupp.sum_embDomain]
  refine Finsupp.sum_congr fun i _ => ?_
  rw [Finsupp.sum_embDomain]
  refine Finsupp.sum_congr fun j _ => ?_
  simp only [hankelMatrix, Fin.valEmbedding_apply, star_trivial]

/-- Todo vetor finitamente suportado em `ℕ` provém de alguma câmera finita. -/
theorem exists_embDomain {x : ℕ →₀ ℝ} {r : ℕ} (hr : x.support ⊆ Finset.range r) :
    ∃ y : Fin r →₀ ℝ, y.embDomain Fin.valEmbedding = x := by
  refine ⟨Finsupp.onFinset Finset.univ (fun i : Fin r => x i.val)
    (fun _ _ => Finset.mem_univ _), ?_⟩
  ext n
  by_cases hn : n < r
  · have h2 := Finsupp.embDomain_apply_self Fin.valEmbedding
      (Finsupp.onFinset Finset.univ (fun i : Fin r => x i.val) (fun _ _ => Finset.mem_univ _))
      (⟨n, hn⟩ : Fin r)
    rw [Finsupp.onFinset_apply] at h2
    exact h2
  · rw [Finsupp.embDomain_notin_range]
    · exact (Finsupp.notMem_support_iff.mp
        (fun hmem => hn (Finset.mem_range.mp (hr hmem)))).symm
    · rintro ⟨i, hi⟩
      rw [Fin.valEmbedding_apply] at hi
      exact hn (hi ▸ i.isLt)

/-- **A passagem ao limite.** A positividade do objeto-limite é exatamente a torre
consistente de positividades finitas das câmeras. -/
theorem hankelForm_nonneg_iff_tower (h : ℕ → ℝ) (s : ℕ) :
    (∀ x : ℕ →₀ ℝ, 0 ≤ hankelForm h s x) ↔ (∀ r, (hankelMatrix h s r).PosSemidef) := by
  constructor
  · intro hpos r
    refine ⟨hankelMatrix_isHermitian h s r, fun y => ?_⟩
    rw [← hankelForm_embDomain]
    exact hpos _
  · intro htower x
    obtain ⟨r, hr⟩ : ∃ r, x.support ⊆ Finset.range r :=
      ⟨x.support.sup id + 1, fun n hn => by
        rw [Finset.mem_range]
        exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hn)⟩
    obtain ⟨y, hy⟩ := exists_embDomain hr
    rw [← hy, hankelForm_embDomain]
    exact (htower r).2 y

#print axioms hankelForm_embDomain
#print axioms hankelForm_nonneg_iff_tower

end
end CarryTiltSlice
