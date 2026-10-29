import RealLedger

namespace CarryTwoEvenJets
open CarrySelfAdjointOperator PhysicalSewing CPFormal.Analytic.Cp
open Filter Topology
open scoped BigOperators ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000

/-- This is a coefficient bound on the SAME quartic, not a new observation metric. -/
theorem polarizedQuartic_norm_le (a b c d : Fin 4 → ℂ) (A B C D : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (_hD : 0 ≤ D)
    (ha : ∀ j, ‖a j‖ ≤ A) (hb : ∀ j, ‖b j‖ ≤ B)
    (hc : ∀ j, ‖c j‖ ≤ C) (hd : ∀ j, ‖d j‖ ≤ D) :
    ‖polarizedQuartic a b c d‖ ≤ 8*A*B*C*D := by
  unfold polarizedQuartic
  calc
    ‖a 0*b 1*c 1*d 2+3*a 0*b 0*c 1*d 3-4*a 0*b 0*c 2*d 2‖ ≤
        (‖a 0*b 1*c 1*d 2‖+‖3*a 0*b 0*c 1*d 3‖)+‖4*a 0*b 0*c 2*d 2‖ :=
      by
        have hs := norm_sub_le (a 0*b 1*c 1*d 2+3*a 0*b 0*c 1*d 3) (4*a 0*b 0*c 2*d 2)
        have ha := norm_add_le (a 0*b 1*c 1*d 2) (3*a 0*b 0*c 1*d 3)
        linarith
    _ ≤ A*B*C*D+3*A*B*C*D+4*A*B*C*D := by
      simp only [norm_mul]
      norm_num
      gcongr <;> first | exact ha _ | exact hb _ | exact hc _ | exact hd _
    _ = 8*A*B*C*D := by ring

theorem quartic_difference (u v : Fin 4 → ℂ) :
    quartic u-quartic v =
      polarizedQuartic (u-v) u u u+polarizedQuartic v (u-v) u u+
      polarizedQuartic v v (u-v) u+polarizedQuartic v v v (u-v) := by
  simp only [quartic,polarizedQuartic,Pi.sub_apply]
  ring

/-- A concrete sufficient error budget for four complete source coefficients.
There is no derivative of 1/F and no positivity premise. -/
theorem quartic_unit_error (u v : Fin 4 → ℂ) (e : ℝ) (he : 0 ≤ e)
    (hu : ∀ j, ‖u j‖ ≤ 1) (hv : ∀ j, ‖v j‖ ≤ 1)
    (herr : ∀ j, ‖u j-v j‖ ≤ e) :
    ‖quartic u-quartic v‖ ≤ 32*e := by
  have hd : ∀ j, ‖(u-v) j‖ ≤ e := herr
  have h1 := polarizedQuartic_norm_le (u-v) u u u e 1 1 1 he (by norm_num) (by norm_num) (by norm_num) hd hu hu hu
  have h2 := polarizedQuartic_norm_le v (u-v) u u 1 e 1 1 (by norm_num) he (by norm_num) (by norm_num) hv hd hu hu
  have h3 := polarizedQuartic_norm_le v v (u-v) u 1 1 e 1 (by norm_num) (by norm_num) he (by norm_num) hv hv hd hu
  have h4 := polarizedQuartic_norm_le v v v (u-v) 1 1 1 e (by norm_num) (by norm_num) (by norm_num) he hv hv hv hd
  rw [quartic_difference]
  calc
    ‖polarizedQuartic (u-v) u u u+polarizedQuartic v (u-v) u u+
        polarizedQuartic v v (u-v) u+polarizedQuartic v v v (u-v)‖ ≤
        ‖polarizedQuartic (u-v) u u u‖+‖polarizedQuartic v (u-v) u u‖+
          ‖polarizedQuartic v v (u-v) u‖+‖polarizedQuartic v v v (u-v)‖ := by
      have h12 := norm_add_le (polarizedQuartic (u-v) u u u) (polarizedQuartic v (u-v) u u)
      have h123 := norm_add_le
        (polarizedQuartic (u-v) u u u+polarizedQuartic v (u-v) u u) (polarizedQuartic v v (u-v) u)
      have h1234 := norm_add_le
        (polarizedQuartic (u-v) u u u+polarizedQuartic v (u-v) u u+polarizedQuartic v v (u-v) u)
        (polarizedQuartic v v v (u-v))
      linarith
    _ ≤ (8*e*1*1*1)+(8*1*e*1*1)+(8*1*1*e*1)+(8*1*1*1*e) :=
      add_le_add (add_le_add (add_le_add h1 h2) h3) h4
    _ = 32*e := by ring

end
end CarryTwoEvenJets
