import OneBlock

namespace CarryFourLeg
open GeometryOfNumbers.Analysis CarrySelfAdjointOperator
open CPFormal.Analytic.Cp NativeCarrySpectralWeyl.Boundary
open scoped ComplexConjugate
noncomputable section
set_option autoImplicit false

def c2LegLogIncrement (m k : ℕ) (epsilon : ℝ) : ℝ :=
  Real.log 2 + c2FiberLogDefect m epsilon (k+1) - c2FiberLogDefect m epsilon k

def c2LegWaveFactor (m k : ℕ) (epsilon : ℝ) (s : ℂ) : ℂ :=
  (2 : ℂ)^(-s) * Complex.exp (-s*((c2FiberLogDefect m epsilon (k+1) -
    c2FiberLogDefect m epsilon k : ℝ) : ℂ))

/-- Literal material one-jet at the existing C2 point. -/
def c2LegJet (m : ℕ) (epsilon : ℝ) (s : ℂ) (k : ℕ) : ℂ × ℂ :=
  let n := c2FiberPoint m epsilon k
  ((n : ℂ)^(-s), (Real.log n : ℂ)*(n : ℂ)^(-s))

/-- Transport of the one-jet, before gradients or bilinear readout.
The logarithmic shear comes from the actual leg increment. -/
def c2LegTransfer (m k : ℕ) (epsilon : ℝ) (s : ℂ) (p : ℂ × ℂ) : ℂ × ℂ :=
  let a := c2LegWaveFactor m k epsilon s
  (a*p.1, a*(p.2+(c2LegLogIncrement m k epsilon : ℂ)*p.1))

theorem c2_leg_jet_step (m k : ℕ) (epsilon : ℝ) (s : ℂ)
    (hm : 0 < m) (hx : 0 < c2FiberPoint m epsilon k)
    (hy : 0 < c2FiberPoint m epsilon (k+1)) :
    c2LegJet m epsilon s (k+1) = c2LegTransfer m k epsilon s (c2LegJet m epsilon s k) := by
  have hw := c2_material_wave_step m epsilon s k hm hx hy
  have hl : (Real.log (c2FiberPoint m epsilon (k+1)) : ℂ) =
      (Real.log (c2FiberPoint m epsilon k) : ℂ) + (c2LegLogIncrement m k epsilon : ℂ) := by
    have h := congrArg (fun r : ℝ => (r : ℂ))
      (c2FiberPoint_log_increment_defect m k hm epsilon hx hy)
    dsimp [c2LegLogIncrement]
    push_cast at h ⊢
    linear_combination h
  apply Prod.ext
  · exact hw
  · change (Real.log (c2FiberPoint m epsilon (k+1)) : ℂ)*
      (c2FiberPoint m epsilon (k+1) : ℂ)^(-s) = _
    rw [hw, hl]
    dsimp [c2LegTransfer, c2LegJet, c2LegWaveFactor]
    ring

/-- Independent material legs generally have different logarithmic shears.
Their exact value-value correction remains in the original Green form. -/
theorem c2_two_leg_green_defect (m k n l : ℕ) (epsilon delta : ℝ)
    (s t : ℂ) (p q : ℂ × ℂ) :
    let a := c2LegWaveFactor m k epsilon s
    let b := c2LegWaveFactor n l delta t
    greenForm (𝕜 := ℂ) (c2LegTransfer m k epsilon s p) (c2LegTransfer n l delta t q) =
      conj a*b*greenForm (𝕜 := ℂ) p q +
      conj a*b*((c2LegLogIncrement m k epsilon - c2LegLogIncrement n l delta : ℝ) : ℂ)*
        inner ℂ p.1 q.1 := by
  dsimp only
  simp only [c2LegTransfer, greenForm, RCLike.inner_apply', map_mul, map_add,
    Complex.conj_ofReal, Complex.ofReal_sub]
  ring

def nativePointJet (n : ℕ) (s : ℂ) : ℂ × ℂ :=
  (natDirichletTerm s n, natLogDirichletTerm s n)

def nativeGradientJet (n : ℕ) (s : ℂ) : ℂ × ℂ :=
  (positiveDirichletGradient s n, positiveLogDirichletGradient s n)

theorem native_gradient_jet_eq (n : ℕ) (s : ℂ) :
    nativeGradientJet n s = nativePointJet (n+2) s - nativePointJet (n+1) s := by
  apply Prod.ext
  · rfl
  · simp only [nativeGradientJet, nativePointJet, positiveLogDirichletGradient,
      positiveLogDirichletValue_eq_natLogDirichletTerm, Prod.snd_sub]

/-- Two retained edges after transporting all three original point jets.
The roles are kept even where the original cells shared a material point. -/
def transportedC2Cell (m : ℕ) (s : ℂ) : (ℂ × ℂ) × (ℂ × ℂ) :=
  (c2LegTransfer m 0 0 s (c2LegJet m 0 s 0) -
    c2LegTransfer m 0 (-1) s (c2LegJet m (-1) s 0),
   c2LegTransfer m 0 1 s (c2LegJet m 1 s 0) -
    c2LegTransfer m 0 0 s (c2LegJet m 0 s 0))

theorem transported_c2_cell_eq (m : ℕ) (hm : 2 ≤ m) (s : ℂ) :
    transportedC2Cell m s =
      (c2LegJet m 0 s 1 - c2LegJet m (-1) s 1,
       c2LegJet m 1 s 1 - c2LegJet m 0 s 1) := by
  have hp : 0 < m := by omega
  have hleft : 0 < c2FiberPoint m (-1) 0 := by
    simp only [c2FiberPoint, pow_zero, one_mul]
    have hmr : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  unfold transportedC2Cell
  rw [← c2_leg_jet_step m 0 0 s hp (c2FiberPoint_center_pos m 0 hp) (c2FiberPoint_center_pos m 1 hp),
    ← c2_leg_jet_step m 0 (-1) s hp hleft (c2FiberPoint_left_pos m 1 hp (by omega)),
    ← c2_leg_jet_step m 0 1 s hp (c2FiberPoint_right_pos m 0 hp) (c2FiberPoint_right_pos m 1 hp)]

theorem one_block_c2_cells_before_step (s : ℂ) :
    ((c2LegJet 2 0 s 0 - c2LegJet 2 (-1) s 0,
       c2LegJet 2 1 s 0 - c2LegJet 2 0 s 0),
     (c2LegJet 3 0 s 0 - c2LegJet 3 (-1) s 0,
       c2LegJet 3 1 s 0 - c2LegJet 3 0 s 0)) =
      ((nativeGradientJet 0 s, nativeGradientJet 1 s),
       (nativeGradientJet 1 s, nativeGradientJet 2 s)) := by
  simp only [native_gradient_jet_eq]
  norm_num [c2LegJet, c2FiberPoint, nativePointJet, natLogDirichletTerm,
    natDirichletTerm, dirichletTerm]

/-- M=1 pilot: the two original C3 boundary cells have centers 2 and 3.
After fixed-radius depth transport they produce g2,g3 and g4,g5, including
their log jets. The original shared middle edge does not stay shared. -/
theorem one_block_c2_cells_after_step (s : ℂ) :
    (transportedC2Cell 2 s, transportedC2Cell 3 s) =
      ((nativeGradientJet 2 s, nativeGradientJet 3 s),
       (nativeGradientJet 4 s, nativeGradientJet 5 s)) := by
  rw [transported_c2_cell_eq 2 (by omega), transported_c2_cell_eq 3 (by omega)]
  simp only [native_gradient_jet_eq]
  norm_num [c2LegJet, c2FiberPoint, nativePointJet, natLogDirichletTerm,
    natDirichletTerm, dirichletTerm]

/-- A raw local regression at s=1 (before camera division/completion).
The transported cells cannot retain the same shared-middle-edge constraint.
This is not a no-go for the completed critical source. -/
theorem one_block_middle_splits_at_one :
    ((transportedC2Cell 2 (1 : ℂ)).2).1 ≠ ((transportedC2Cell 3 (1 : ℂ)).1).1 := by
  have h := one_block_c2_cells_after_step (1 : ℂ)
  have hl := congrArg Prod.fst h
  have hr := congrArg Prod.snd h
  dsimp only at hl hr
  rw [hl, hr]
  norm_num [nativeGradientJet, positiveDirichletGradient, natDirichletTerm,
    dirichletTerm, Complex.cpow_neg_one]

end
end CarryFourLeg
