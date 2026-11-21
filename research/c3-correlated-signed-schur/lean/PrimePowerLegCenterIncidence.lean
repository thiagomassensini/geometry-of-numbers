import PrimeDepthMangoldtBracket
import Mathlib.Tactic

/-!
Finite integer primitive-divisor incidence atom for one C2 bracket.

The support coefficient of an arithmetic divisor d>=3 is +1 when
d hits one leg and -2 when it hits the center. These are LITERAL
source coefficients, before inserting positive von Mangoldt amplitudes.

They are not positive quadratic energies, and the completed source has
other signed/archimedean channels.
-/
namespace CarryWheelNativeSignedGate

/-- Incidence of one primitive divisor in the C2 center/legs stencil. -/
def c2DivisorLegCenterAtom (d c : ℕ) : ℤ :=
  (if d ∣ c-1 then 1 else 0) -
    2 * (if d ∣ c then 1 else 0) +
    (if d ∣ c+1 then 1 else 0)

/-- Any nontrivial divisor landing at the center misses both adjacent legs:
the center coefficient is exactly -2. -/
theorem c2DivisorLegCenterAtom_center (d c : ℕ)
    (hd : 2 ≤ d) (hc : 1 ≤ c) (hdiv : d ∣ c) :
    c2DivisorLegCenterAtom d c = -2 := by
  have hm : ¬ d ∣ c-1 := by
    intro h
    have hsub : d ∣ c-(c-1) := Nat.dvd_sub hdiv h
    have hone : c-(c-1)=1 := by omega
    have h1 : d ∣ 1 := by simpa [hone] using hsub
    have hdle : d ≤ 1 := Nat.le_of_dvd (by norm_num) h1
    omega
  have hp : ¬ d ∣ c+1 := by
    intro h
    have hsub : d ∣ (c+1)-c := Nat.dvd_sub h hdiv
    have hone : (c+1)-c=1 := by omega
    have h1 : d ∣ 1 := by simpa [hone] using hsub
    have hdle : d ≤ 1 := Nat.le_of_dvd (by norm_num) h1
    omega
  simp [c2DivisorLegCenterAtom,hm,hp,hdiv]

/-- For any divisor d>=3 on the left leg, it cannot simultaneously
hit the center or the right leg. Its coefficient is +1. -/
theorem c2DivisorLegCenterAtom_leftLeg (d c : ℕ)
    (hd : 3 ≤ d) (hc : 1 ≤ c) (hdiv : d ∣ c-1) :
    c2DivisorLegCenterAtom d c = 1 := by
  have hm : ¬ d ∣ c := by
    intro h
    have hsub : d ∣ c-(c-1) := Nat.dvd_sub h hdiv
    have hone : c-(c-1)=1 := by omega
    have h1 : d ∣ 1 := by simpa [hone] using hsub
    have hdle : d ≤ 1 := Nat.le_of_dvd (by norm_num) h1
    omega
  have hp : ¬ d ∣ c+1 := by
    intro h
    have hsub : d ∣ (c+1)-(c-1) := Nat.dvd_sub h hdiv
    have htwo : (c+1)-(c-1)=2 := by omega
    have h2 : d ∣ 2 := by simpa [htwo] using hsub
    have hdle : d ≤ 2 := Nat.le_of_dvd (by norm_num) h2
    omega
  simp [c2DivisorLegCenterAtom,hm,hp,hdiv]

/-- The same +1 atom on the right leg. -/
theorem c2DivisorLegCenterAtom_rightLeg (d c : ℕ)
    (hd : 3 ≤ d) (hc : 1 ≤ c) (hdiv : d ∣ c+1) :
    c2DivisorLegCenterAtom d c = 1 := by
  have hm : ¬ d ∣ c := by
    intro h
    have hsub : d ∣ (c+1)-c := Nat.dvd_sub hdiv h
    have hone : (c+1)-c=1 := by omega
    have h1 : d ∣ 1 := by simpa [hone] using hsub
    have hdle : d ≤ 1 := Nat.le_of_dvd (by norm_num) h1
    omega
  have hp : ¬ d ∣ c-1 := by
    intro h
    have hsub : d ∣ (c+1)-(c-1) := Nat.dvd_sub hdiv h
    have htwo : (c+1)-(c-1)=2 := by omega
    have h2 : d ∣ 2 := by simpa [htwo] using hsub
    have hdle : d ≤ 2 := Nat.le_of_dvd (by norm_num) h2
    omega
  simp [c2DivisorLegCenterAtom,hm,hp,hdiv]

end CarryWheelNativeSignedGate
