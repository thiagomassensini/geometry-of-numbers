import NativeCarrySpectralWeyl.Infinite.CameraCompletion
import CarrySelfAdjointOperator.CompletedNativeCameraUniversality

/-! The existing all-camera metric does not descend through equality of the
completed scalar observations. Camera probes are not interchangeable state
coordinates merely because their completed responses coincide. -/
namespace CarryCameraObservationAudit
open NativeCarrySpectralWeyl.Infinite NativeCarrySpectralWeyl.Camera
open NativeCarrySpectralWeyl.Finite NativeCarrySpectralWeyl.Limits
open CarrySelfAdjointOperator
open scoped InnerProductSpace BigOperators
noncomputable section

def cameraTwo : CameraIndex := ⟨2, by decide⟩
def cameraFour : CameraIndex := ⟨4, by decide⟩

theorem camera_two_four_gram :
    gramKernel cameraTwo cameraTwo = 6 ∧
    gramKernel cameraTwo cameraFour = 10 ∧
    gramKernel cameraFour cameraTwo = 10 ∧
    gramKernel cameraFour cameraFour = 22 := by
  norm_num [cameraTwo, cameraFour, gramKernel, periodicMeanKernel, pairPeriod,
    cameraSlope, cameraLabel, periodicProductMean, periodicProductSum,
    profile, c2Profile, evenProfile, dvdIndicator, Finset.sum_range_succ]

/-- The exact metric detects an independent direction between these camera probes. -/
theorem camera_two_four_distance :
    ‖cameraVector cameraTwo-cameraVector cameraFour‖^2 = 8 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_sub_left, inner_sub_right, inner_cameraVector]
  obtain ⟨h22,h24,h42,h44⟩ := camera_two_four_gram
  rw [h22,h24,h42,h44]
  norm_num

/-- Both complete normalized observations are nevertheless identical, for every cutoff. -/
theorem completed_camera_two_four_equal (cutoff : ℕ) :
    normalizedCompletedNativeCameraCharacteristic 2 cutoff =
      normalizedCompletedNativeCameraCharacteristic 4 cutoff := by
  rw [normalizedCompletedNativeCameraCharacteristic_eq (by decide : 2 ≤ 2),
    normalizedCompletedNativeCameraCharacteristic_eq (by decide : 2 ≤ 4)]

/-- No energy on scalar responses can preserve this existing camera norm on differences.
This is a specific failure of scalar-response equivalence as physical redundancy. -/
theorem no_camera_energy_descent (cutoff : ℕ) :
    ¬ ∃ energy : (ℝ → ℂ) → ℝ, energy 0 = 0 ∧
      energy (normalizedCompletedNativeCameraCharacteristic 2 cutoff -
        normalizedCompletedNativeCameraCharacteristic 4 cutoff) =
        ‖cameraVector cameraTwo-cameraVector cameraFour‖^2 := by
  rintro ⟨energy,hzero,h⟩
  rw [completed_camera_two_four_equal, sub_self, hzero, camera_two_four_distance] at h
  norm_num at h

end
end CarryCameraObservationAudit
