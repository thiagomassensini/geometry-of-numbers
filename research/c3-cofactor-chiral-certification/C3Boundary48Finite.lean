import C3Acceleration48

namespace CarryC3Tail

noncomputable section
set_option autoImplicit false

/-- The doubled cell identity telescopes on every finite step-three window,
retaining both boundary values and the full 26th-difference remainder. -/
theorem c3_acceleration48_finite (f : ℕ → ℂ) (a N : ℕ) :
    (∑ k ∈ Finset.range N, fd 2 f (a+3*k)) =
      c3Boundary48 f a - c3Boundary48 f (a+3*N) +
        (1/(729^2:ℂ))*∑ k ∈ Finset.range N, fd 26 f (a+3*k) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ,ih,Finset.sum_range_succ,c3_acceleration48_cell]
      rw [show a+3*(N+1)=a+3*N+3 by omega]
      ring

#print axioms c3_acceleration48_finite

end
end CarryC3Tail
