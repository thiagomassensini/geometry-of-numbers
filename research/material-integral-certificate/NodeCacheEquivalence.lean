import CachedSourceProgram
import ArgNodeChecks
import ModeNodeChecks

/-! Cached numbers accelerate the proof checker only. These exact equalities
preserve the entire interval program, including signed Taylor terms and tails. -/
namespace CarryIntegralCertificate
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
attribute [local irreducible] finiteModeBox tailModeBox fullModeBox fullThetaMomentBox
  cachedFiniteModeBox cachedTailModeBox cachedFullModeBox cachedFullThetaMomentBox

theorem argumentBox_eq_cached (m : Fin 3) (j : ℕ) (hj : j ≤ thetaCertificateCellCount m.val) :
    argumentBox m.val (gridBox j 64) = cachedArgumentNode m.val j :=
  argument_node_checks m ⟨j,by omega⟩

theorem modeBox_eq_cached (m : Fin 3) (j : ℕ) (hj : j ≤ thetaCertificateCellCount m.val) :
    modeBox m.val (gridBox j 64) = cachedModeNode m.val j := by
  unfold modeBox
  rw [argumentBox_eq_cached m j hj]
  exact mode_node_checks m ⟨j,by omega⟩

theorem majorantBox_eq_cached (m : Fin 3) (n j : ℕ)
    (hj : j ≤ thetaCertificateCellCount m.val) :
    majorantBox m.val n (gridBox j 64) = cachedMajorantBox m.val n j := by
  unfold majorantBox cachedMajorantBox
  rw [argumentBox_eq_cached m j hj]

theorem taylorMassBox_eq_cached (m : Fin 3) (n p j : ℕ)
    (hj : j ≤ thetaCertificateCellCount m.val) :
    taylorMassBox m.val n p (gridBox j 64) (gridBox (j+1) 64) =
      cachedTaylorMassBox m.val n p j := by
  unfold taylorMassBox cachedTaylorMassBox
  rw [argumentBox_eq_cached m j hj,modeBox_eq_cached m j hj]

theorem cellBox_eq_cached (m : Fin 3) (n p j : ℕ)
    (hj : j < thetaCertificateCellCount m.val) :
    cellBox m.val n p (gridBox j 64) (gridBox (j+1) 64) = cachedCellBox m.val n p j := by
  unfold cellBox cachedCellBox
  rw [taylorMassBox_eq_cached m n p j (by omega),
    majorantBox_eq_cached m (n+1) (j+1) (by omega),modeBox_eq_cached m j (by omega)]

theorem Box.sum_congr (f g : ℕ → Box) (n : ℕ) (h : ∀ j < n, f j = g j) :
    Box.sum f n = Box.sum g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Box.sum,Box.sum,ih (fun j hj => h j (by omega)),h n (by omega)]

theorem finiteModeBox_eq_cached (m : Fin 3) (n p : ℕ) :
    finiteModeBox m.val n p 64 (thetaCertificateCellCount m.val) = cachedFiniteModeBox m.val n p := by
  unfold finiteModeBox cachedFiniteModeBox
  exact Box.sum_congr _ _ _ (fun j hj => cellBox_eq_cached m n p j hj)

theorem decayBox_eq_cached (m : Fin 3) (p j : ℕ)
    (hj : j ≤ thetaCertificateCellCount m.val) :
    decayBox m.val p (gridBox j 64) = cachedDecayBox m.val p j := by
  unfold decayBox cachedDecayBox
  rw [argumentBox_eq_cached m j hj]

theorem tailModeBox_eq_cached (m : Fin 3) (p j : ℕ)
    (hj : j ≤ thetaCertificateCellCount m.val) :
    tailModeBox m.val p (gridBox j 64) = cachedTailModeBox m.val p j := by
  unfold tailModeBox cachedTailModeBox
  rw [modeBox_eq_cached m j hj,decayBox_eq_cached m p j hj]

theorem fullModeBox_eq_cached (m : Fin 3) (n p : ℕ) :
    fullModeBox m.val n p 64 (thetaCertificateCellCount m.val) = cachedFullModeBox m.val n p := by
  unfold fullModeBox cachedFullModeBox
  rw [finiteModeBox_eq_cached m n p,tailModeBox_eq_cached m p _ le_rfl]

theorem fullThetaMomentBox_eq_cached (p : ℕ) :
    fullThetaMomentBox p = cachedFullThetaMomentBox p := by
  unfold fullThetaMomentBox cachedFullThetaMomentBox
  have h0 := fullModeBox_eq_cached (0:Fin 3) 15 p
  have h1 := fullModeBox_eq_cached (1:Fin 3) 15 p
  have h2 := fullModeBox_eq_cached (2:Fin 3) 15 p
  norm_num [thetaCertificateCellCount] at h0 h1 h2
  rw [h0,h1,h2]

end CarryIntegralCertificate
