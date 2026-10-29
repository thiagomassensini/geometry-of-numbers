import StencilPair
import CenteredDifference

namespace CarryCenteredStirling
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- Exact factorial change of variables needed to merge the two ordered
physical Cauchy legs into a centered binomial sum. -/
theorem shifted_factorial_binomial (m n i : ℕ) (hi : i ≤ m) :
    (m.choose i:ℂ)*((i+1).factorial:ℂ)/
      ((m.factorial:ℂ)*((i+n+2).factorial:ℂ)) =
      ((m+n+2).choose (n+i+2):ℂ)*((i:ℂ)+1)/((m+n+2).factorial:ℂ) := by
  have hs : m+n+2-(n+i+2)=m-i := by omega
  have hk : n+i+2 ≤ m+n+2 := by omega
  have h1 : (m.choose i:ℂ)*(i.factorial:ℂ)*((m-i).factorial:ℂ)=(m.factorial:ℂ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hi
  have h2 : ((m+n+2).choose (n+i+2):ℂ)*((i+n+2).factorial:ℂ)*((m-i).factorial:ℂ)=
      ((m+n+2).factorial:ℂ) := by
    have hh := Nat.choose_mul_factorial_mul_factorial hk
    rw [hs] at hh
    have he : n+i+2=i+n+2 := by omega
    rw [he] at hh
    rw [he]
    exact_mod_cast hh
  have hm : (m.factorial:ℂ)≠0 := by exact_mod_cast Nat.factorial_ne_zero m
  have hd : ((i+n+2).factorial:ℂ)≠0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hN : ((m+n+2).factorial:ℂ)≠0 := by exact_mod_cast Nat.factorial_ne_zero _
  rw [Nat.factorial_succ i]
  push_cast
  field_simp
  rw [← h2,← h1]
  ring

end
end CarryCenteredStirling
