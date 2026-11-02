import NativeLogOperatorBridge

/-!
# `‖L^m v‖²` como norma genuína em `ℓ²(ℕ,ℂ)`

Constrói, no espaço de Hilbert **real** do operador (`InfiniteRealSpectralHilbert = ℓ²(ℕ,ℂ)`),
o elemento `L^m v` — a `m`-ésima potência espectral (multiplicação coordenada a coordenada por
`log(n+1)^m`, cf. `infiniteRealSpectralGenerator_apply`) do vetor `v = Σ_k √w_k e_{c_k−1}`.
Suas coordenadas são `(log c_k)^m √w_k` nas posições `c_k − 1 = 3k+2`, e `0` fora delas.

Prova:
`(-1)^m G^{(2m)}(0) = Σ_k w_k (log c_k)^{2m} = ‖L^m v‖²`
agora como **norma ℓ² literal** do elemento `tiltLpVector m` (não apenas soma de quadrados).

Honestidade: `tiltLpVector m` é a potência espectral explícita (multiplicação por `log(n+1)^m`,
que é o cálculo funcional do gerador, com `m=1` = `nativeLogGenerator` em `nativeLogGenerator_cell_eigenvalue`).
Não se constrói a iteração da `LinearPMap` não limitada `nativeLogGenerator^[m]`; usa-se o vetor
espectral explícito no mesmo `ℓ²(ℕ,ℂ)`.

Não modifica nenhum módulo anterior.
-/

namespace CarryTiltSlice
open CPFormal.Analytic.Cp CarrySelfAdjointOperator
open scoped BigOperators Topology ENNReal
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- Coordenada de `L^m v` na posição `n`: a célula `k` se `n = 3k+2 = c_k − 1`, senão `0`. -/
def tiltLpCoord (m n : ℕ) : ℂ :=
  if n % 3 = 2 then ((tiltSpectralVector m (n / 3) : ℝ) : ℂ) else 0

theorem tiltLpCoord_cell (m k : ℕ) :
    tiltLpCoord m (3 * k + 2) = ((tiltSpectralVector m k : ℝ) : ℂ) := by
  unfold tiltLpCoord
  rw [if_pos (by omega : (3 * k + 2) % 3 = 2), show (3 * k + 2) / 3 = k by omega]

theorem tiltLpCoord_zero_of_not (m n : ℕ) (h : n % 3 ≠ 2) : tiltLpCoord m n = 0 := by
  unfold tiltLpCoord; rw [if_neg h]

theorem tiltLpCoord_normSq_cell (m k : ℕ) :
    ‖tiltLpCoord m (3 * k + 2)‖ ^ 2 = mixedTiltTerm m k := by
  rw [tiltLpCoord_cell, Complex.norm_real, Real.norm_eq_abs, sq_abs, tiltSpectralVector_sq]

/-- Reindexação pelo suporte `{3k+2}`: a soma dos quadrados das coordenadas é o jato misto. -/
theorem tiltLpCoord_hasSum_normSq (m : ℕ) :
    HasSum (fun n => ‖tiltLpCoord m n‖ ^ 2) (∑' k, mixedTiltTerm m k) := by
  refine (hasSum_iff_hasSum_of_ne_zero_bij
    (i := fun x : Function.support (fun k => mixedTiltTerm m k) => 3 * (x : ℕ) + 2)
    ?hinj ?hsupp ?hval).mpr (mixedTiltTerm_summable m).hasSum
  case hinj =>
    intro a b h
    simp only at h
    exact Subtype.ext (by omega)
  case hsupp =>
    intro n hn
    have hnz : tiltLpCoord m n ≠ 0 := by
      intro h
      exact hn (by show ‖tiltLpCoord m n‖ ^ 2 = 0; rw [h]; simp)
    have hmod : n % 3 = 2 := by
      by_contra h; exact hnz (tiltLpCoord_zero_of_not m n h)
    have hdiv : 3 * (n / 3) + 2 = n := by omega
    have hvne : tiltSpectralVector m (n / 3) ≠ 0 := by
      intro h0
      apply hnz
      unfold tiltLpCoord; rw [if_pos hmod, h0]; simp
    refine ⟨⟨n / 3, ?_⟩, hdiv⟩
    show mixedTiltTerm m (n / 3) ≠ 0
    rw [← tiltSpectralVector_sq]
    exact pow_ne_zero 2 hvne
  case hval =>
    intro x
    show ‖tiltLpCoord m (3 * (x : ℕ) + 2)‖ ^ 2 = mixedTiltTerm m (x : ℕ)
    exact tiltLpCoord_normSq_cell m (x : ℕ)

theorem tiltLpCoord_memℓp (m : ℕ) : Memℓp (tiltLpCoord m) 2 := by
  apply memℓp_gen
  refine ((tiltLpCoord_hasSum_normSq m).summable).congr (fun n => ?_)
  rw [show ((2 : ℝ≥0∞).toReal) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- `L^m v` como elemento genuíno de `ℓ²(ℕ,ℂ)` (o espaço do operador). -/
def tiltLpVector (m : ℕ) : InfiniteRealSpectralHilbert :=
  ⟨tiltLpCoord m, tiltLpCoord_memℓp m⟩

theorem tiltLpVector_coe (m n : ℕ) :
    (tiltLpVector m : ℕ → ℂ) n = tiltLpCoord m n := rfl

/-- A norma ℓ² ao quadrado do vetor espectral é o jato misto. -/
theorem tiltLpVector_normSq (m : ℕ) :
    ‖tiltLpVector m‖ ^ 2 = ∑' k, mixedTiltTerm m k := by
  have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  have h := lp.norm_rpow_eq_tsum hp (tiltLpVector m)
  rw [show ((2 : ℝ≥0∞).toReal) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h
  rw [h, tsum_congr (fun n => by
    show ‖(tiltLpVector m : ℕ → ℂ) n‖ ^ ((2 : ℕ) : ℝ) = ‖tiltLpCoord m n‖ ^ 2
    rw [Real.rpow_natCast]; rfl)]
  exact (tiltLpCoord_hasSum_normSq m).tsum_eq

/-- **Jets pares do tilt = `‖L^m v‖²`** como norma ℓ² literal no espaço do operador. -/
theorem tilt_jet_eq_lp_normSq (m : ℕ) :
    ((-1 : ℂ) ^ m * iteratedDeriv (2 * m)
        (fun t : ℝ => infiniteMixedTiltResponse (t:ℂ)) 0).re
      = ‖tiltLpVector m‖ ^ 2 := by
  rw [tiltLpVector_normSq]
  exact infinite_mixed_tilt_identity m

/-- A norma é estritamente positiva: o vetor espectral é não nulo em cada ordem. -/
theorem tiltLpVector_normSq_pos (m : ℕ) : 0 < ‖tiltLpVector m‖ ^ 2 := by
  rw [tiltLpVector_normSq]; exact mixedTiltTerm_tsum_pos m

#print axioms tilt_jet_eq_lp_normSq
#print axioms tiltLpVector_normSq_pos

end
end CarryTiltSlice
