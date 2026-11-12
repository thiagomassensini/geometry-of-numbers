import C3FiniteCoefficients

namespace CarryC3Tail

noncomputable section
set_option autoImplicit false

/-- Composition of forward differences adds their orders. -/
theorem fd_comp (m n : ℕ) (f : ℕ → ℂ) :
    ∀ a, fd m (fun k => fd n f k) a = fd (m + n) f a := by
  induction m with
  | zero =>
      intro a
      simp [fd]
  | succ m ih =>
      intro a
      rw [fd_succ, ih (a + 1), ih a]
      calc
        _ = fd (m+n+1) f a := by rw [fd_shift_one]; ring
        _ = fd (m+1+n) f a := by
          rw [show m+n+1 = m+1+n by omega]

/-- The doubled acceleration polynomial with the denominator `729^2`
cleared. It applies in particular to the indeterminate of `Polynomial ℚ`.
The middle factor is `729 * B(D)` in the forward-difference basis. -/
theorem c3_acceleration48_polynomial {R : Type*} [CommRing R] (D : R) :
    729^2 * D^2 =
      (1 - (1 + D)^3) *
        (-243*D + 243*D^2 - 162*D^3 + 81*D^4 - 27*D^5 +
          9*D^7 - 9*D^8 + 6*D^9 - 3*D^10 + D^11) *
        (729 + D^12) + D^26 := by
  ring

/-- Doubled boundary polynomial B(D)(1+D^12/729), kept in its original
forward-difference form so the exact cell identity follows by reusing the
already checked C3 acceleration. -/
def c3Boundary48 (f : ℕ → ℂ) (a : ℕ) : ℂ :=
  c3Boundary f a + (1/729:ℂ) * c3Boundary (fun n => fd 12 f n) a

theorem c3_acceleration48_cell (f : ℕ → ℂ) (a : ℕ) :
    fd 2 f a = c3Boundary48 f a - c3Boundary48 f (a+3) +
      (1/(729^2:ℂ))*fd 26 f a := by
  have h0 := c3_acceleration_cell f a
  have h12 := c3_acceleration_cell (fun n => fd 12 f n) a
  simp only [fd_comp] at h12
  unfold c3Boundary48
  linear_combination h0 + (1/729:ℂ) * h12

#print axioms c3_acceleration48_polynomial
#print axioms c3_acceleration48_cell

end
end CarryC3Tail
