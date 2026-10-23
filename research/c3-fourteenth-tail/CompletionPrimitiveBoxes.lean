import SamplePrimitiveBoxes
namespace CarryC3Boxes
set_option maxHeartbeats 10000000
set_option maxRecDepth 20000
def piLogReference : Box := ⟨(228945977169880034828517/200000000000000000000000),(114472988584940017414577/100000000000000000000000)⟩
def piAmplitudeReference : Box := ⟨(46945346529058905178627/62500000000000000000000),(751125544464942482859093/1000000000000000000000000)⟩
def chartAmplitudeReference : Box := ⟨(866025403784438646763723/500000000000000000000000),(216506350946109661690931/125000000000000000000000)⟩
def logThreeBox : Box := sampleLogReference ⟨2,by omega⟩
theorem pi_log_evaluator_check : piLogBox.Subset piLogReference := by decide +kernel
theorem pi_amplitude_range : -4 ≤ (bmul (Box.point (-1/4)) piLogReference).lo ∧
    (bmul (Box.point (-1/4)) piLogReference).hi ≤ 4 := by decide +kernel
theorem chart_amplitude_range : -4 ≤ (bmul (Box.point (1/2)) logThreeBox).lo ∧
    (bmul (Box.point (1/2)) logThreeBox).hi ≤ 4 := by decide +kernel
theorem pi_amplitude_check : (expBox (bmul (Box.point (-1/4)) piLogReference)).Subset piAmplitudeReference := by decide +kernel
theorem chart_amplitude_check : (expBox (bmul (Box.point (1/2)) logThreeBox)).Subset chartAmplitudeReference := by decide +kernel
theorem pi_log_reference_contains : piLogReference.Contains (Real.log Real.pi) :=
  Box.subset_contains pi_log_evaluator_check pi_log_box
theorem log_three_reference_contains : logThreeBox.Contains (Real.log 3) := by
  simpa only [logThreeBox,Fin.val_mk,Nat.reduceAdd,Nat.cast_ofNat] using sample_log_reference_contains ⟨2,by omega⟩
theorem pi_amplitude_reference_contains : piAmplitudeReference.Contains (Real.exp (-Real.log Real.pi/4)) := by
  apply Box.subset_contains pi_amplitude_check
  have h := bmul_contains (Box.point_contains (-1/4)) pi_log_reference_contains
  have he : ((-1/4:ℚ):ℝ)*Real.log Real.pi = -Real.log Real.pi/4 := by norm_num; ring
  rw [he] at h
  exact exp_box h pi_amplitude_range.1 pi_amplitude_range.2
theorem chart_amplitude_reference_contains : chartAmplitudeReference.Contains (Real.exp (Real.log 3/2)) := by
  apply Box.subset_contains chart_amplitude_check
  have h := bmul_contains (Box.point_contains (1/2)) log_three_reference_contains
  have he : ((1/2:ℚ):ℝ)*Real.log 3 = Real.log 3/2 := by norm_num; ring
  rw [he] at h
  exact exp_box h chart_amplitude_range.1 chart_amplitude_range.2
end CarryC3Boxes
