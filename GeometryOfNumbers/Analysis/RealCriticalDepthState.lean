import GeometryOfNumbers.Analysis.RealQuadraticPlane
import GeometryOfNumbers.Analysis.RealQuadraticAmplitude
import GeometryOfNumbers.Geometry.BalancedCarryDepthCrosswalk

/-!
# The plane state of an already selected depth amplitude

The seed uses the existing amplitude, then arbitrary rotation preserves its
energy. Its indices are capacity, depth, and angle, not a quantity's label.
The balanced-center bridge records support of the SAME depth index; support
is not required for the algebraic energy identity itself. No new selection
argument for the half exponent occurs in this module.
-/

namespace GeometryOfNumbers.Analysis

open Foundation Geometry

noncomputable section

def realCriticalDepthSeed (b k : ℕ) (hb : 0 < b) : RealPlaneState :=
  (realCriticalAmplitude b k hb, 0)

theorem realCriticalDepthSeed_energy_eq_amplitude_sq (b k : ℕ) (hb : 0 < b) :
    realPlaneEnergy (realCriticalDepthSeed b k hb) = realCriticalAmplitude b k hb ^ 2 := by
  simp [realPlaneEnergy, realCriticalDepthSeed]

theorem realCriticalDepthSeed_energy (b k : ℕ) (hb : 0 < b) :
    realPlaneEnergy (realCriticalDepthSeed b k hb) = realDepthMass b k hb := by
  rw [realCriticalDepthSeed_energy_eq_amplitude_sq]
  exact realCriticalAmplitude_sq_eq_realDepthMass b k hb

theorem realCriticalAmplitude_pos (b k : ℕ) (hb : 0 < b) :
    0 < realCriticalAmplitude b k hb := by
  rw [realCriticalAmplitude_eq_rpow]
  exact Real.rpow_pos_of_pos (Nat.cast_pos.mpr hb) _

def realCriticalDepthState (b k : ℕ) (hb : 0 < b) (theta : ℝ) : RealPlaneState :=
  rotateRealPlane theta (realCriticalDepthSeed b k hb)

theorem realCriticalDepthState_eq_coordinates
    (b k : ℕ) (hb : 0 < b) (theta : ℝ) :
    realCriticalDepthState b k hb theta =
      (realCriticalAmplitude b k hb * Real.cos theta,
        realCriticalAmplitude b k hb * Real.sin theta) := by
  simp [realCriticalDepthState, rotateRealPlane, realCriticalDepthSeed]

theorem realCriticalDepthState_energy (b k : ℕ) (hb : 0 < b) (theta : ℝ) :
    realPlaneEnergy (realCriticalDepthState b k hb theta) = realDepthMass b k hb := by
  unfold realCriticalDepthState
  rw [rotateRealPlane_energy]
  exact realCriticalDepthSeed_energy b k hb

theorem realCriticalDepthState_zero_angle (b k : ℕ) (hb : 0 < b) :
    realCriticalDepthState b k hb 0 = realCriticalDepthSeed b k hb :=
  rotateRealPlane_zero _

theorem realCriticalDepthSeed_zero_depth (b : ℕ) (hb : 0 < b) :
    realCriticalDepthSeed b 0 hb = (1, 0) := by
  rw [realCriticalDepthSeed, realCriticalAmplitude_zero]

theorem realCriticalDepthState_zero_depth_energy (b : ℕ) (hb : 0 < b) (theta : ℝ) :
    realPlaneEnergy (realCriticalDepthState b 0 hb theta) = 1 := by
  rw [realCriticalDepthState_energy, realDepthMass_zero]

theorem realCriticalDepthSeed_capacity_one (k : ℕ) :
    realCriticalDepthSeed 1 k Nat.zero_lt_one = (1, 0) := by
  rw [realCriticalDepthSeed, realCriticalAmplitude_one]

theorem realCriticalDepthState_capacity_one_energy (k : ℕ) (theta : ℝ) :
    realPlaneEnergy (realCriticalDepthState 1 k Nat.zero_lt_one theta) = 1 := by
  rw [realCriticalDepthState_energy, realDepthMass_one]

/-- The support hypothesis records provenance of the chosen index, not an
algebraic requirement of the energy theorem. It is intentionally unused. -/
theorem balancedCarryDepth_realState_energy (b n k : ℕ) (hodd : IsOddCapacity b)
    (_hdepth : HasIntegerCarryDepthAtLeast b (balancedCarryCenter b n hodd) k)
    (theta : ℝ) :
    realPlaneEnergy (realCriticalDepthState b k (oddCapacity_pos hodd) theta) =
      realDepthMass b k (oddCapacity_pos hodd) :=
  realCriticalDepthState_energy b k (oddCapacity_pos hodd) theta

/-- Joint provenance: the canonical channel exposes the supported level,
and its plane energy realizes the formal share already derived at that level.
No new mass of a quantity is defined. -/
theorem balancedCarryDepth_realState_realizes_formalMass
    (b n k : ℕ) (hodd : IsOddCapacity b)
    (hdepth : HasIntegerCarryDepthAtLeast b (balancedCarryCenter b n hodd) k)
    (theta : ℝ) :
    HasIntegerCarryDepthAtLeast b ((n : Int) - balancedCarryOffset b n hodd) k ∧
      (canonicalResidualDepthMass b k (oddCapacity_pos hodd)).numerator = 1 ∧
      (canonicalResidualDepthMass b k (oddCapacity_pos hodd)).denominator = b ^ k ∧
      realPlaneEnergy (realCriticalDepthState b k (oddCapacity_pos hodd) theta) =
        realizeCountingShare (canonicalResidualDepthMass b k (oddCapacity_pos hodd)) := by
  have hprovenance := balancedCarry_depth_and_mass_at_same_index b n k hodd hdepth
  exact ⟨hprovenance.1, hprovenance.2.1, hprovenance.2.2,
    realCriticalDepthState_energy b k (oddCapacity_pos hodd) theta⟩

end

end GeometryOfNumbers.Analysis
