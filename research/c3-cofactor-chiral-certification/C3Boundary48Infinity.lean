import InfiniteC3Tail
import C3Boundary48Finite
import C3Power26Series

namespace CarryC3Tail
open CarrySelfAdjointOperator PhysicalSewing CarryTwoEvenJets CPFormal.Analytic.Cp
open Set Filter Topology
open scoped BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000

/-- A fixed forward difference of the C3 sample still tends to zero along the
original step-three address lattice. -/
theorem c3_boundary_fd_at_infinity (r M : ℕ) (w : ℂ)
    (hw : ‖w‖ ≤ (1/2:ℝ)) :
    Tendsto (fun N => c3Boundary
      (fun n => fd r (fun m => c3Sample m w) n) (3*M+2+3*N)) atTop (nhds 0) := by
  have h (j : ℕ) (hj : 0 < j) : Tendsto
      (fun N => fd j (fun k => fd r (fun m => c3Sample m w) k) (3*M+2+3*N))
        atTop (nhds 0) := by
    have hnative := native_fd_at_infinity (j+r) M (by omega) w hw
    have heq : (fun N => fd j (fun k => fd r (fun m => c3Sample m w) k)
        (3*M+2+3*N)) =
      (fun N => fd (j+r) (fun m => c3Sample m w) (3*M+2+3*N)) := by
      funext N
      exact fd_comp j r (fun m => c3Sample m w) (3*M+2+3*N)
    rw [heq]
    exact hnative
  have h1 := (h 1 (by norm_num)).const_mul (-(1/3:ℂ))
  have h2 := h1.add ((h 2 (by norm_num)).const_mul (1/3:ℂ))
  have h3 := h2.sub ((h 3 (by norm_num)).const_mul (2/9:ℂ))
  have h4 := h3.add ((h 4 (by norm_num)).const_mul (1/9:ℂ))
  have h5 := h4.sub ((h 5 (by norm_num)).const_mul (1/27:ℂ))
  have h7 := h5.add ((h 7 (by norm_num)).const_mul (1/81:ℂ))
  have h8 := h7.sub ((h 8 (by norm_num)).const_mul (1/81:ℂ))
  have h9 := h8.add ((h 9 (by norm_num)).const_mul (2/243:ℂ))
  have h10 := h9.sub ((h 10 (by norm_num)).const_mul (1/243:ℂ))
  have hh := h10.add ((h 11 (by norm_num)).const_mul (1/729:ℂ))
  simpa only [c3Boundary,mul_zero,add_zero,sub_zero] using hh

theorem c3_boundary48_at_infinity (M : ℕ) (w : ℂ)
    (hw : ‖w‖ ≤ (1/2:ℝ)) :
    Tendsto (fun N => c3Boundary48 (fun n => c3Sample n w) (3*M+2+3*N))
      atTop (nhds 0) := by
  have h0 := c3_boundary_fd_at_infinity 0 M w hw
  have h12 := c3_boundary_fd_at_infinity 12 M w hw
  simpa only [c3Boundary48, fd_zero, zero_add, mul_zero] using
    h0.add (h12.const_mul (1/(729:ℂ)))

/-- Finite-window form of the doubled C3 acceleration on the original
bracket, with the literal left and right boundary terms. -/
theorem native_c3_tail_window48 (M N : ℕ) (w : ℂ) :
    (∑ k ∈ Finset.range N,
      realCpSaturatedBracket 3 (k+M) (operatorHeightParameter w)) =
      c3Boundary48 (fun n => c3Sample n w) (3*M+2) -
        c3Boundary48 (fun n => c3Sample n w) (3*M+2+3*N) +
          (1/(729^2:ℂ))*∑ k ∈ Finset.range N,
            fd 26 (fun n => c3Sample n w) (3*(k+M)+2) := by
  simp_rw [native_c3_cell_fd,
    show ∀ k : ℕ, 3*(k+M)+2=3*M+2+3*k by omega]
  simpa [Nat.mul_add, Nat.add_assoc] using
    (c3_acceleration48_finite (fun n => c3Sample n w) (3*M+2) N)

/-- Exact infinite tail identity for the doubled order-26 boundary. -/
theorem native_c3_tail_acceleration48 (M : ℕ) (w : ℂ)
    (hw : ‖w‖ ≤ (1/2:ℝ)) :
    realCpBracketCutoffTail 3 M (operatorHeightParameter w) =
      c3Boundary48 (fun n => c3Sample n w) (3*M+2) +
        (1/(729^2:ℂ))*∑' k : ℕ,
          fd 26 (fun n => c3Sample n w) (3*(k+M)+2) := by
  have hs : -1 < (operatorHeightParameter w).re :=
    height_mem_bracket_half_plane w (lt_of_le_of_lt hw (by norm_num))
  have hcell := (summable_norm_realCpSaturatedBracket 3 (by norm_num) hs).comp_injective
    (show Function.Injective (fun k : ℕ => k+M) from fun _ _ h => Nat.add_right_cancel h)
  have hl := hcell.of_norm.hasSum.tendsto_sum_nat
  have hr : Tendsto (fun N =>
      c3Boundary48 (fun n => c3Sample n w) (3*M+2) -
        c3Boundary48 (fun n => c3Sample n w) (3*M+2+3*N) +
          (1/(729^2:ℂ))*∑ k ∈ Finset.range N,
            fd 26 (fun n => c3Sample n w) (3*(k+M)+2)) atTop
      (nhds (c3Boundary48 (fun n => c3Sample n w) (3*M+2) +
        (1/(729^2:ℂ))*∑' k : ℕ,
          fd 26 (fun n => c3Sample n w) (3*(k+M)+2))) := by
    simpa only [sub_zero] using
      (tendsto_const_nhds.sub (c3_boundary48_at_infinity M w hw)).add
        ((c3_twenty_sixth_summable M w hw).of_norm.hasSum.tendsto_sum_nat
          |>.const_mul (1/(729^2:ℂ)))
  apply tendsto_nhds_unique hl
  exact hr.congr' (.of_forall (fun N => (native_c3_tail_window48 M N w).symm))

#print axioms c3_boundary48_at_infinity
#print axioms native_c3_tail_window48
#print axioms native_c3_tail_acceleration48

end
end CarryC3Tail
