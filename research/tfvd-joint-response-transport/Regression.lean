import SourceApplication
import DiagonalControl

open CarryTfvdJoint
open CarrySelfAdjointOperator PhysicalSewing
noncomputable section

-- Composition at an intermediate zero must retain the multiplied factors.
example : jointNumerator (fun z : ℂ => z) (fun _ => 1) (fun _ => 0) (-1) 1 = -2*Complex.I := by
  norm_num [jointNumerator]
  ring

-- Independent endpoints need a conjugated, symmetric log-jet crossing.
example (T L B U V C : ℂ) :
    polarizedNumerator T L B U V C =
      (starRingEnd ℂ) T*U*(C-(starRingEnd ℂ) B) +
        Complex.I*((starRingEnd ℂ) T*V+(starRingEnd ℂ) L*U) := rfl

-- PR41's old-prefix condition remains IsUnit, with no hidden positivity premise.
#check critical_jointKernel_tendsto
#check Control.full_original_form_negative
#check Control.radial_diagonal_pos
