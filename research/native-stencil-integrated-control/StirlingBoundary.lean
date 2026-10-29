import FiniteVelocityBudget
import CarrySelfAdjointOperator.NewtonStirlingTransport
import Mathlib.Data.Nat.Choose.Cast

namespace CarryCenteredStirling
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

/-- Two steps above the diagonal, without assuming a sign for any moment. -/
theorem stirling_second_diagonal_two (n : ℕ) :
    (24:ℚ)*(Nat.stirlingSecond (n+2) n:ℚ) =
      (n:ℚ)*((n:ℚ)+1)*((n:ℚ)+2)*(3*(n:ℚ)+1) := by
  induction n with
  | zero => norm_num [Nat.stirlingSecond]
  | succ n ih =>
    have hs := Nat.stirlingSecond_succ_succ (n+2) n
    have hchoose : (Nat.stirlingSecond (n+2) (n+1):ℚ)=((n:ℚ)+2)*((n:ℚ)+1)/2 := by
      rw [Nat.stirlingSecond_succ_self_left]
      rw [Nat.cast_choose_two]
      push_cast
      ring
    have hcast := congrArg (fun x : ℕ => (x:ℚ)) hs
    push_cast at hcast
    rw [hchoose] at hcast
    push_cast
    nlinarith

/-- The coefficient predicted by the centered Newton calculation agrees
algebraically with the two-variance formula for all real orders. -/
theorem centered_coefficient_polynomial (m n : ℚ) :
    let N := m+n+2
    let K := n+1
    ((N+2)*(N+1)/2)*K^2-(N+2)*K*(N*(N+1)/2)+
      N*(N+1)*(N+2)*(3*N+1)/24 =
        (m+1)*(m+2)*(2*m+3)/12 + (n+1)*(n+2)*(2*n+3)/12 +
          (((m+1)*(m+2)/2)-((n+1)*(n+2)/2))^2/2 := by
  dsimp
  ring


/-- All-order identification of the centered Stirling coefficient with
Lambda, pending only the independent stencil-to-centered-sum transport. -/
theorem stirling_coefficient_eq_lambda (m n : ℕ) :
    let N : ℕ := m+n+2
    let R : ℚ := (N:ℚ)
    let K : ℚ := (n:ℚ)+1
    ((R+2)*(R+1)/2)*K^2-(R+2)*K*(Nat.stirlingSecond (N+1) N:ℚ)+
      (Nat.stirlingSecond (N+2) N:ℚ) =
        ((m:ℚ)+1)*((m:ℚ)+2)*(2*(m:ℚ)+3)/12 +
        ((n:ℚ)+1)*((n:ℚ)+2)*(2*(n:ℚ)+3)/12 +
          ((((m:ℚ)+1)*((m:ℚ)+2)/2)-(((n:ℚ)+1)*((n:ℚ)+2)/2))^2/2 := by
  dsimp
  have hS := stirling_second_diagonal_two (m+n+2)
  have hT : (Nat.stirlingSecond (m+n+2+1) (m+n+2):ℚ) =
      (((m:ℚ)+(n:ℚ)+3)*((m:ℚ)+(n:ℚ)+2))/2 := by
    rw [Nat.stirlingSecond_succ_self_left, Nat.cast_choose_two]
    push_cast
    ring
  rw [hT]
  push_cast at hS ⊢
  nlinarith [centered_coefficient_polynomial (m:ℚ) (n:ℚ)]

end
end CarryCenteredStirling
