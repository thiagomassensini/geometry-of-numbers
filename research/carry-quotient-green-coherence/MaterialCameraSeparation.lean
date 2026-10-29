import NativeCarrySpectralWeyl.Finite.Gram

/-! Exact finite material observability from the ORIGINAL native camera profiles.
Indices n are material addresses, not jet orders. Complex coefficients retain
both quadratures. No target moment, Gram factor, or new profile is supplied. -/
namespace CarryMaterialCameraSeparation
open NativeCarrySpectralWeyl.Camera
open scoped BigOperators
noncomputable section

def materialReadout (N b : ℕ) (a : ℕ → ℂ) : ℂ :=
  ∑ n ∈ Finset.range (N+1), a n * (profile b n : ℂ)

def divisibilityReadout (N d : ℕ) (a : ℕ → ℂ) : ℂ :=
  ∑ n ∈ Finset.range (N+1), a n * (dvdIndicator d n : ℂ)

def totalReadout (N : ℕ) (a : ℕ → ℂ) : ℂ :=
  ∑ n ∈ Finset.range (N+1), a n

/-- The large odd camera reads the exact total on the bounded material support. -/
theorem odd_camera_total (N : ℕ) (hN : 1 ≤ N) (a : ℕ → ℂ) (hzero : a 0 = 0) :
    materialReadout N (2*N+1) a = totalReadout N a := by
  unfold materialReadout totalReadout
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hn0 : n = 0
  · simp [hn0,hzero]
  · have hnpos : 0 < n := by omega
    have hnb : n < 2*N+1 := by have := Finset.mem_range.mp hn; omega
    have hnot : ¬ 2*N+1 ∣ n := by
      intro hd
      have := Nat.le_of_dvd hnpos hd
      omega
    have hodd : Odd (2*N+1) := ⟨N, by omega⟩
    rw [profile_of_odd (by omega : 2*N+1 ≠ 2) hodd]
    simp [oddProfile,dvdIndicator,hnot]

/-- Native even cameras couple only d and 2d in divisor coordinates. -/
theorem even_camera_divisibility (N d : ℕ) (hd : 2 ≤ d) (a : ℕ → ℂ) :
    materialReadout N (2*d) a = totalReadout N a +
      divisibilityReadout N d a - ((2*d+2 : ℕ) : ℂ)*divisibilityReadout N (2*d) a := by
  have heven : Even (2*d) := ⟨d, by omega⟩
  have hhalf : (2*d)/2 = d := by omega
  have hp (n : ℕ) : (profile (2*d) n : ℂ) =
      1 + (dvdIndicator d n : ℂ) - ((2*d+2 : ℕ) : ℂ)*(dvdIndicator (2*d) n : ℂ) := by
    rw [profile_of_even (by omega : 2*d ≠ 2) heven]
    simp only [evenProfile, hhalf]
    push_cast
    ring
  unfold materialReadout totalReadout divisibilityReadout
  simp_rw [hp, mul_sub, mul_add, mul_one]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  ring

theorem divisibility_above_support (N d : ℕ) (hd : N < d)
    (a : ℕ → ℂ) (hzero : a 0 = 0) : divisibilityReadout N d a = 0 := by
  unfold divisibilityReadout
  apply Finset.sum_eq_zero
  intro n hn
  by_cases hn0 : n = 0
  · simp [hn0,hzero]
  · have hnot : ¬ d ∣ n := by
      intro hdn
      have := Nat.le_of_dvd (by omega : 0 < n) hdn
      have := Finset.mem_range.mp hn
      omega
    simp [dvdIndicator,hnot]

/-- The finite camera equations determine every divisor readout, with no sign assumption. -/
theorem divisor_readouts_zero (N : ℕ) (hN : 1 ≤ N) (a : ℕ → ℂ) (hzero : a 0 = 0)
    (hodd : materialReadout N (2*N+1) a = 0)
    (heven : ∀ d, 2 ≤ d → d ≤ N → materialReadout N (2*d) a = 0) :
    ∀ d, 1 ≤ d → divisibilityReadout N d a = 0 := by
  have htotal : totalReadout N a = 0 := by
    rwa [odd_camera_total N hN a hzero] at hodd
  have hstep : ∀ k d, N < d+k → 2 ≤ d → divisibilityReadout N d a = 0 := by
    intro k
    induction k with
    | zero =>
      intro d hbound _
      exact divisibility_above_support N d (by omega) a hzero
    | succ k ih =>
      intro d hbound hd
      by_cases hlarge : N < d
      · exact divisibility_above_support N d hlarge a hzero
      · have htwo := ih (2*d) (by omega) (by omega)
        have hcamera := heven d hd (by omega)
        rw [even_camera_divisibility N d hd a, htotal, htwo] at hcamera
        simpa only [mul_zero,zero_add,sub_zero] using hcamera
  intro d hd
  by_cases hone : d = 1
  · subst d
    simpa [divisibilityReadout,totalReadout,dvdIndicator] using htotal
  · exact hstep (N+1) d (by omega) (by omega)

/-- Divisibility observations are triangular and separate every bounded input. -/
theorem divisibility_separates (N : ℕ) (a : ℕ → ℂ) (hzero : a 0 = 0)
    (hdiv : ∀ d, 1 ≤ d → divisibilityReadout N d a = 0) :
    ∀ n, n ≤ N → a n = 0 := by
  have hstep : ∀ k d, N < d+k → 1 ≤ d → d ≤ N → a d = 0 := by
    intro k
    induction k with
    | zero => intro d hbound _ hdN; omega
    | succ k ih =>
      intro d hbound hd hdN
      have hsum : divisibilityReadout N d a = a d := by
        unfold divisibilityReadout
        rw [Finset.sum_eq_single d]
        · simp [dvdIndicator]
        · intro n hn hne
          by_cases hn0 : n = 0
          · simp [hn0,hzero]
          · by_cases hdn : d ∣ n
            · have hle := Nat.le_of_dvd (by omega : 0 < n) hdn
              have hnN := Finset.mem_range.mp hn
              rw [ih n (by omega) (by omega) (by omega), zero_mul]
            · simp [dvdIndicator,hdn]
        · intro hn
          exact (hn (Finset.mem_range.mpr (by omega))).elim
      exact hsum.symm.trans (hdiv d hd)
  intro n hn
  by_cases hn0 : n = 0
  · simpa only [hn0] using hzero
  · exact hstep (N+1) n (by omega) (by omega) hn

/-- N original camera observations suffice for all N complex material coefficients.
The camera list is the large odd camera and the even cameras 4,6,...,2N. -/
theorem finite_camera_separation (N : ℕ) (hN : 1 ≤ N) (a : ℕ → ℂ) (hzero : a 0 = 0)
    (hodd : materialReadout N (2*N+1) a = 0)
    (heven : ∀ d, 2 ≤ d → d ≤ N → materialReadout N (2*d) a = 0) :
    ∀ n, n ≤ N → a n = 0 :=
  divisibility_separates N a hzero (divisor_readouts_zero N hN a hzero hodd heven)

/-- One coherent family, on all finite-support material data. This is an
observation of the old profiles, not a replacement source or moment sequence. -/
def finiteMaterialObservation (a : ℕ →₀ ℂ) (b : ℕ) : ℂ :=
  a.sum (fun n z => z * (profile b n : ℂ))

theorem bounded_readout_eq (a : ℕ →₀ ℂ) (N b : ℕ)
    (hbound : ∀ n ∈ a.support, n ≤ N) :
    materialReadout N b a = finiteMaterialObservation a b := by
  classical
  change (∑ n ∈ Finset.range (N+1), a n * (profile b n : ℂ)) =
    ∑ n ∈ a.support, a n * (profile b n : ℂ)
  symm
  apply Finset.sum_subset
  · intro n hn
    exact Finset.mem_range.mpr (by have := hbound n hn; omega)
  · intro n _ hn
    rw [Finsupp.notMem_support_iff.mp hn,zero_mul]

/-- Joint vanishing in the ORIGINAL camera family implies zero finite material data. -/
theorem all_cameras_finite_separate (a : ℕ →₀ ℂ) (hzero : a 0 = 0)
    (hcamera : ∀ b, 2 ≤ b → finiteMaterialObservation a b = 0) : a = 0 := by
  classical
  let N := a.support.sup id + 1
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hbound (n : ℕ) (hn : n ∈ a.support) : n ≤ N := by
    have h := Finset.le_sup (f := id) hn
    dsimp [N]
    exact h.trans (Nat.le_succ _)
  have hodd : materialReadout N (2*N+1) a = 0 := by
    rw [bounded_readout_eq a N (2*N+1) hbound]
    exact hcamera _ (by omega)
  have heven (d : ℕ) (hd : 2 ≤ d) (_ : d ≤ N) :
      materialReadout N (2*d) a = 0 := by
    rw [bounded_readout_eq a N (2*d) hbound]
    exact hcamera _ (by omega)
  have hsep := finite_camera_separation N hN a hzero hodd heven
  ext n
  by_cases hn : n ∈ a.support
  · exact hsep n (hbound n hn)
  · exact Finsupp.notMem_support_iff.mp hn

theorem finiteMaterialObservation_sub (a b : ℕ →₀ ℂ) (camera : ℕ) :
    finiteMaterialObservation (a-b) camera =
      finiteMaterialObservation a camera-finiteMaterialObservation b camera := by
  simpa only [finiteMaterialObservation,Finsupp.linearCombination_apply,smul_eq_mul] using
    map_sub (Finsupp.linearCombination ℂ (fun n => (profile camera n : ℂ))) a b

/-- Equality of the complete camera observations is exact equality of finite
material data; no independent finite contribution is lost. -/
theorem all_cameras_finite_injective (a b : ℕ →₀ ℂ) (ha : a 0 = 0) (hb : b 0 = 0)
    (hcamera : ∀ camera, 2 ≤ camera →
      finiteMaterialObservation a camera = finiteMaterialObservation b camera) : a = b := by
  apply sub_eq_zero.mp
  apply all_cameras_finite_separate
  · simp [ha,hb]
  · intro camera hc
    rw [finiteMaterialObservation_sub,hcamera camera hc,sub_self]

end
end CarryMaterialCameraSeparation
