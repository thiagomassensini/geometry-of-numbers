import NativeNewtonInput

namespace CarryNativeBinomial
open CarrySelfAdjointOperator
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

/-- The same explicit coefficient of one finitely supported ORIGINAL source,
written without choosing a cutoff. It is not a moment or a new physical state. -/
def sourceNewtonCoefficient (k : ℕ) (x : ℕ →₀ ℂ) (m : ℕ) : ℂ :=
  nativeSourceJetOrderPhase m * (m.factorial:ℂ) *
    canonicalCompletedC3RadialSecondStep k^m *
      x.sum (fun r z => (Nat.choose r m:ℂ)*z)

/-- Finite charts restrict one source-coefficient family exactly. -/
theorem newton_coordinates_of_support (n k : ℕ) (x : ℕ →₀ ℂ)
    (hx : x.support ⊆ Finset.range (2*n)) (m : Fin (2*n)) :
    newtonCoordinates n k (fun r : Fin (2*n) => x r) m=
      sourceNewtonCoefficient k x m := by
  have he := Finsupp.sum_of_support_subset x hx
    (fun r z => (Nat.choose r (m:ℕ):ℂ)*z) (by intro r _; simp)
  unfold newtonCoordinates sourceNewtonCoefficient
  rw [he, ← Fin.sum_univ_eq_sum_range
    (fun r : ℕ => (Nat.choose r (m:ℕ):ℂ)*x r)]

/-- Increasing a prefix containing the same source does not change its old
coefficients. This is exact coherence, not an infinite positivity claim. -/
theorem newton_coordinates_prefix_coherent (n p k : ℕ) (x : ℕ →₀ ℂ)
    (hn : x.support ⊆ Finset.range (2*n)) (hp : x.support ⊆ Finset.range (2*p))
    (i : Fin (2*n)) (j : Fin (2*p)) (hij : (i:ℕ)=(j:ℕ)) :
    newtonCoordinates n k (fun r : Fin (2*n) => x r) i=
      newtonCoordinates p k (fun r : Fin (2*p) => x r) j := by
  rw [newton_coordinates_of_support n k x hn i,
    newton_coordinates_of_support p k x hp j, hij]

/-- A source supported below N has no Newton coefficient of order ≥N. -/
theorem source_newton_above_support (k N m : ℕ) (x : ℕ →₀ ℂ)
    (hx : x.support ⊆ Finset.range N) (hm : N ≤ m) :
    sourceNewtonCoefficient k x m=0 := by
  have hs : x.sum (fun r z => (Nat.choose r m:ℂ)*z)=0 := by
    apply Finset.sum_eq_zero
    intro r hr
    have hrN := Finset.mem_range.mp (hx hr)
    simp [Nat.choose_eq_zero_of_lt (show r < m from by omega)]
  simp only [sourceNewtonCoefficient, hs, mul_zero]

theorem newton_coordinates_above_support (n k N : ℕ) (x : ℕ →₀ ℂ)
    (hx : x.support ⊆ Finset.range (2*n)) (hN : x.support ⊆ Finset.range N)
    (m : Fin (2*n)) (hm : N ≤ (m:ℕ)) :
    newtonCoordinates n k (fun r : Fin (2*n) => x r) m=0 := by
  rw [newton_coordinates_of_support n k x hx m]
  exact source_newton_above_support k N m x hN hm

end
end CarryNativeBinomial
