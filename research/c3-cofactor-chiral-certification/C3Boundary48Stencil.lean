import C3Boundary48Infinity

namespace CarryC3Tail

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000

/-- The rational 24-point stencil obtained by expanding the doubled boundary
polynomial `B(D) * (1 + D^12/729)` in powers of `1 + D`. -/
def boundary48Weight (k : Fin 24) : ℚ := ![
  (531440:ℚ)/729^2, -1062856/729^2, 531116/729^2, 534040/729^2,
  -1077806/729^2, 596896/729^2, 303810/729^2, -420006/729^2,
  -965379/729^2, 3428360/729^2, -5731741/729^2, 6760781/729^2,
  -6229340/729^2, 4668859/729^2, -2896919/729^2, 1496820/729^2,
  -642876/729^2, 227631/729^2, -65455/729^2, 14924/729^2,
  -2599/729^2, 325/729^2, -26/729^2, 1/729^2] k

/-- Exact 24-sample stencil for the doubled C3 boundary. -/
theorem boundary48_stencil (f : ℕ → ℂ) (a : ℕ) :
    c3Boundary48 f a =
      ∑ k : Fin 24, (boundary48Weight k : ℂ) * f (a + k.val) := by
  unfold c3Boundary48
  rw [boundary_stencil, boundary_stencil]
  simp only [fd, fwdDiff_iter_eq_sum_shift]
  norm_num [boundaryWeight, boundary48Weight, Fin.sum_univ_succ,
    Finset.sum_range_succ, zsmul_eq_mul, Nat.choose_succ_succ,
    Nat.add_assoc]
  ring

#print axioms boundary48_stencil

end
end CarryC3Tail
