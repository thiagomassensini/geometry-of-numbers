import SourceProvenance
import FourthDifference
import Mathlib.Algebra.Group.ForwardDiff

namespace CarryC3Tail
open CarrySelfAdjointOperator PhysicalSewing CarryTwoEvenJets CPFormal.Analytic.Cp
open Filter Topology
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- The existing Mathlib forward difference, always at step one. -/
abbrev fd {A : Type*} [AddCommMonoid A] [One A] (n : ℕ) (f : A → ℂ) (a : A) : ℂ :=
  (fwdDiff (1:A))^[n] f a

theorem fd_zero {A : Type*} [AddCommMonoid A] [One A] (f : A → ℂ) (a : A) :
    fd 0 f a = f a := rfl

theorem fd_succ {A : Type*} [AddCommMonoid A] [One A] (n : ℕ) (f : A → ℂ) (a : A) :
    fd (n+1) f a = fd n f (a+1)-fd n f a := by
  rw [fd,Function.iterate_succ_apply']
  rfl

theorem fd_shift_one (n : ℕ) (f : ℕ → ℂ) (a : ℕ) :
    fd n f (a+1) = fd n f a+fd (n+1) f a := by rw [fd_succ]; ring

theorem fd_shift_two (n : ℕ) (f : ℕ → ℂ) (a : ℕ) :
    fd n f (a+2) = fd n f a+2*fd (n+1) f a+fd (n+2) f a := by
  rw [show a+2=(a+1)+1 by omega,fd_shift_one,fd_shift_one,fd_shift_one]
  ring

theorem fd_shift_three (n : ℕ) (f : ℕ → ℂ) (a : ℕ) :
    fd n f (a+3) = fd n f a+3*fd (n+1) f a+3*fd (n+2) f a+fd (n+3) f a := by
  rw [show a+3=(a+2)+1 by omega,fd_shift_one,fd_shift_two,fd_shift_two]
  ring

theorem fd_two (f : ℕ → ℂ) (a : ℕ) :
    fd 2 f a = f (a+2)-2*f (a+1)+f a := by
  simp only [show 2=1+1 by rfl,fd_succ,fd_zero]
  rw [show a+1+1=a+2 by omega]
  ring

/-- Exact C3 boundary polynomial. Its coefficients are forced by division
of -D by 3+3D+D², through degree 11; they do not fit any moments. -/
def c3Boundary (f : ℕ → ℂ) (a : ℕ) : ℂ :=
  -(1/3:ℂ)*fd 1 f a+(1/3:ℂ)*fd 2 f a-(2/9:ℂ)*fd 3 f a+
  (1/9:ℂ)*fd 4 f a-(1/27:ℂ)*fd 5 f a+
  (1/81:ℂ)*fd 7 f a-(1/81:ℂ)*fd 8 f a+
  (2/243:ℂ)*fd 9 f a-(1/243:ℂ)*fd 10 f a+(1/729:ℂ)*fd 11 f a

theorem c3_acceleration_cell (f : ℕ → ℂ) (a : ℕ) :
    fd 2 f a = c3Boundary f a-c3Boundary f (a+3)+(1/729:ℂ)*fd 14 f a := by
  unfold c3Boundary
  simp only [fd_shift_three]
  norm_num only [Nat.reduceAdd]
  ring

/-- Every endpoint and remainder survives the finite summation identity. -/
theorem c3_acceleration_finite (f : ℕ → ℂ) (a N : ℕ) :
    (∑ k ∈ Finset.range N, fd 2 f (a+3*k)) =
      c3Boundary f a-c3Boundary f (a+3*N)+
        (1/729:ℂ)*∑ k ∈ Finset.range N, fd 14 f (a+3*k) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ,ih,Finset.sum_range_succ,c3_acceleration_cell]
    rw [show a+3*(N+1)=a+3*N+3 by omega]
    ring

/-- The material wave at its original address and phase. -/
def c3Sample (n : ℕ) (w : ℂ) : ℂ := (n:ℂ)^(-operatorHeightParameter w)

theorem c3_sample_eq_generic_power (n : ℕ) (w : ℂ) :
    c3Sample n w = CarryFourthTail.complexSample n w := by
  unfold c3Sample CarryFourthTail.complexSample
    GeometryOfNumbers.Analysis.BaseTwoCompletion.baseTwoComplexMaterialExponent operatorHeightParameter
  congr 1
  ring

/-- Literal addresses 3m+2,3m+3,3m+4. This is the required crosswalk;
no step-four camera or vertical-depth index is identified with C3. -/
theorem native_c3_cell_fd (m : ℕ) (w : ℂ) :
    realCpSaturatedBracket 3 m (operatorHeightParameter w) =
      fd 2 (fun n => c3Sample n w) (3*m+2) := by
  rw [realCpSaturatedBracket_three_eq_values,fd_two]
  simp only [natDirichletTerm,dirichletTerm,c3Sample]
  rw [show 3*m+2+2=3*m+4 by omega,show 3*m+2+1=3*m+3 by omega]
  push_cast
  ring

theorem native_c3_tail_window (M N : ℕ) (w : ℂ) :
    (∑ k ∈ Finset.range N, realCpSaturatedBracket 3 (k+M) (operatorHeightParameter w)) =
      c3Boundary (fun n => c3Sample n w) (3*M+2)-
      c3Boundary (fun n => c3Sample n w) (3*M+2+3*N)+
      (1/729:ℂ)*∑ k ∈ Finset.range N, fd 14 (fun n => c3Sample n w) (3*(k+M)+2) := by
  simp_rw [native_c3_cell_fd,show ∀ k : ℕ, 3*(k+M)+2=3*M+2+3*k by omega]
  exact c3_acceleration_finite _ _ _

end
end CarryC3Tail
