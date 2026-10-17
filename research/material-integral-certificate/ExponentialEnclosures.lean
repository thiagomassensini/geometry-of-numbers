import FixedInterval

/-! Executable enclosures implementing the Mathlib exponential remainder rule at a cheaper auxiliary precision. Closed arithmetic is checked by the Lean kernel. -/
namespace CarryIntegralCertificate
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- An auxiliary computational precision; this scaling belongs only to the
exponential enclosure algorithm, never to the physical source or its metric. -/
private theorem exp_scaled20_bounds {x : ℝ} (hx : 0 ≤ x) (hxu : x ≤ 128) :
    (∑ r ∈ Finset.range 20, (x/128)^r/(r.factorial:ℝ))^128 ≤ Real.exp x ∧
      Real.exp x ≤ ((∑ r ∈ Finset.range 20, (x/128)^r/(r.factorial:ℝ))+
        (x/128)^20*21/((Nat.factorial 20:ℝ)*20))^128 := by
  have hy : 0 ≤ x/128 := by positivity
  have hy1 : x/128 ≤ 1 := by linarith
  have hl := Real.sum_le_exp_of_nonneg hy 20
  have hu := Real.exp_bound' hy hy1 (n := 20) (by norm_num)
  have hu' : Real.exp (x/128) ≤ (∑ r ∈ Finset.range 20, (x/128)^r/(r.factorial:ℝ))+
      (x/128)^20*21/((Nat.factorial 20:ℝ)*20) := by
    convert hu using 1
    norm_num
  have he : Real.exp x = (Real.exp (x/128))^128 := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [he]
  exact ⟨pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => by positivity)) hl 128,
    pow_le_pow_left₀ (Real.exp_nonneg _) hu' 128⟩

/-- Twenty Taylor terms for exp(x/128), with every operation rounded out. -/
def Box.expTaylor (i : Box) : Box :=
  Box.sum (fun r => ((i.div (.point 128)).pow r).div (.point (r.factorial:ℤ))) 20

def Box.expRemainder (i : Box) : Box :=
  (((i.div (.point 128)).pow 20).mul (.point 21)).div
    (.point ((Nat.factorial 20:ℤ)*20))

/-- `all` propagates an out-of-range or failed numerical calculation. -/
def Box.exp : Box → Box
  | .all => .all
  | .finite a b => if 0 ≤ a ∧ b ≤ 128*intervalScale then
      let i := Box.finite a b
      let s := i.expTaylor
      (s.squares 7).outer ((s.add i.expRemainder).squares 7)
    else .all

attribute [irreducible] Box.expTaylor Box.expRemainder

theorem mem_expTaylor {i : Box} {x : ℝ} (hx : i.Mem x) :
    i.expTaylor.Mem (∑ r ∈ Finset.range 20, (x/128)^r/(r.factorial:ℝ)) := by
  unfold Box.expTaylor
  apply mem_sum
  intro r _
  have h := mem_div (mem_pow (mem_div hx (mem_point 128)) r)
    (mem_point (r.factorial:ℤ))
  simpa only [Int.cast_natCast,Int.cast_ofNat] using h


theorem mem_expRemainder {i : Box} {x : ℝ} (hx : i.Mem x) :
    i.expRemainder.Mem ((x/128)^20*21/((Nat.factorial 20:ℝ)*20)) := by
  unfold Box.expRemainder
  have h := mem_div (mem_mul (mem_pow (mem_div hx (mem_point 128)) 20)
    (mem_point 21)) (mem_point ((Nat.factorial 20:ℤ)*20))
  simpa only [Int.cast_natCast,Int.cast_ofNat,Int.cast_mul] using h


theorem mem_exp {i : Box} {x : ℝ} (hx : i.Mem x) : i.exp.Mem (Real.exp x) := by
  cases i with
  | all => trivial
  | finite a b =>
    by_cases hab : 0 ≤ a ∧ b ≤ 128*intervalScale
    · have hs : (0:ℝ) < (intervalScale:ℝ) := by norm_num [intervalScale]
      have ha : (0:ℝ) ≤ (a:ℝ) := by exact_mod_cast hab.1
      have hb : (b:ℝ) ≤ 128*(intervalScale:ℝ) := by exact_mod_cast hab.2
      have hxl : 0 ≤ x := by nlinarith only [hx.1,ha,hs]
      have hxu : x ≤ 128 := by nlinarith only [hx.2,hb,hs]
      have hbound := exp_scaled20_bounds hxl hxu
      have hl := mem_squares (mem_expTaylor hx) 7
      have hu := mem_squares (mem_add (mem_expTaylor hx) (mem_expRemainder hx)) 7
      rw [Box.exp,if_pos hab]
      change ((Box.finite a b).expTaylor.squares 7).outer
        (((Box.finite a b).expTaylor.add (Box.finite a b).expRemainder).squares 7)
          |>.Mem (Real.exp x)
      simp only [show (2:ℕ)^7=128 from rfl] at hl hu
      exact mem_outer hl hu hbound.1 hbound.2
    · simp [Box.exp,hab,Box.Mem]

end CarryIntegralCertificate
