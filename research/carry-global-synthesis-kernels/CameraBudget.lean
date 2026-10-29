import MaterialCameraSeparation
import GeometryOfNumbers.Analysis.CarryMaterialSourceRealization
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-! The PR39 separating observations have a repeated common component.
Its extraction is exact on finite material data; no replacement metric,
camera weights, or canonical moment family is introduced. -/
namespace CarryGlobalCameraBudget
open CarryMaterialCameraSeparation NativeCarrySpectralWeyl.Camera
open GeometryOfNumbers.Analysis GeometryOfNumbers.Analysis.BaseTwoCompletion
open Filter
open scoped BigOperators Topology
noncomputable section

def finiteTotal (a : ℕ →₀ ℂ) : ℂ := a.sum (fun _ z => z)

private theorem profile_large (N b n : ℕ) (hb : 2*N+2 < b) (hn : n ≤ N) (hnpos : 0 < n) :
    profile b n = 1 := by
  have hnb : ¬ b ∣ n := by
    intro h
    have := Nat.le_of_dvd hnpos h
    omega
  have hhalf : ¬ b/2 ∣ n := by
    intro h
    have := Nat.le_of_dvd hnpos h
    omega
  by_cases ho : Odd b
  · rw [profile_of_odd (by omega) ho]
    simp [oddProfile,dvdIndicator,hnb]
  · rw [profile_of_even (by omega) (Nat.not_odd_iff_even.mp ho)]
    simp [evenProfile,dvdIndicator,hnb,hhalf]

/-- Every sufficiently large camera repeats exactly the same total. -/
theorem large_camera_total (a : ℕ →₀ ℂ) (ha : a 0 = 0) (N b : ℕ)
    (hbound : ∀ n ∈ a.support, n ≤ N) (hb : 2*N+2 < b) :
    finiteMaterialObservation a b = finiteTotal a := by
  classical
  unfold finiteMaterialObservation finiteTotal
  apply Finset.sum_congr rfl
  intro n hn
  dsimp only
  have hnpos : 0 < n := by
    have hne := Finsupp.mem_support_iff.mp hn
    by_contra h
    have : n = 0 := by omega
    exact hne (this ▸ ha)
  rw [profile_large N b n hb (hbound n hn) hnpos]
  simp

/-- The centered observations have finite support; this is an algebraic
separation of a repeated component, not an identification of a positive Gram. -/
theorem centered_observations_finite (a : ℕ →₀ ℂ) (ha : a 0 = 0) :
    (Function.support (fun j : ℕ => finiteMaterialObservation a (j+2)-finiteTotal a)).Finite := by
  classical
  let N := a.support.sup id+1
  have hbound (n : ℕ) (hn : n ∈ a.support) : n ≤ N :=
    (Finset.le_sup (f := id) hn).trans (Nat.le_succ _)
  apply (Finset.range (2*N+3)).finite_toSet.subset
  intro j hj
  by_contra hnot
  have hjbound : 2*N+3 ≤ j := by simpa only [Finset.mem_coe,Finset.mem_range,not_lt] using hnot
  exact hj (sub_eq_zero.mpr (large_camera_total a ha N (j+2) hbound (by omega)))

/-- A natural unweighted sum over all cameras is finite exactly when the
repeated total vanishes. Finite joint injectivity alone did not supply this. -/
theorem camera_energy_summable_iff (a : ℕ →₀ ℂ) (ha : a 0 = 0) :
    Summable (fun j : ℕ => ‖finiteMaterialObservation a (j+2)‖^2) ↔ finiteTotal a = 0 := by
  classical
  let N := a.support.sup id+1
  have hbound (n : ℕ) (hn : n ∈ a.support) : n ≤ N :=
    (Finset.le_sup (f := id) hn).trans (Nat.le_succ _)
  have he : (fun j : ℕ => ‖finiteMaterialObservation a ((j+(2*N+3))+2)‖^2) =
      fun _ : ℕ => ‖finiteTotal a‖^2 := by
    funext j
    rw [large_camera_total a ha N _ hbound (by omega)]
  rw [← summable_nat_add_iff (2*N+3),he]
  simp only [summable_const_iff,sq_eq_zero_iff,norm_eq_zero]

/-- A seed already present in the native material geometry is repeated in every camera. -/
theorem seed_camera_observation (b : ℕ) (hb : 2 ≤ b) :
    finiteMaterialObservation (Finsupp.single 1 (1 : ℂ)) b = 1 := by
  have hprofile : profile b 1 = 1 := by
    by_cases h2 : b = 2
    · subst b
      norm_num [profile,c2Profile,dvdIndicator]
    · by_cases ho : Odd b
      · rw [profile_of_odd h2 ho]
        simp [oddProfile,dvdIndicator,show ¬ b ∣ 1 by intro h; have := Nat.le_of_dvd (by decide : 0 < 1) h; omega]
      · have he := Nat.not_odd_iff_even.mp ho
        have hnb : ¬ b ∣ 1 := by intro h; have := Nat.le_of_dvd (by decide : 0 < 1) h; omega
        have hhalf : ¬ b/2 ∣ 1 := by
          intro h
          have := Nat.le_of_dvd (by decide : 0 < 1) h
          obtain ⟨k,hk⟩ := he
          omega
        rw [profile_of_even h2 he]
        simp [evenProfile,dvdIndicator,hnb,hhalf]
  simp [finiteMaterialObservation,hprofile]

theorem seed_camera_energy_prefix (M : ℕ) :
    (∑ j ∈ Finset.range M, ‖finiteMaterialObservation (Finsupp.single 1 (1 : ℂ)) (j+2)‖^2) = M := by
  have he (j : ℕ) : finiteMaterialObservation (Finsupp.single 1 (1 : ℂ)) (j+2) = 1 :=
    seed_camera_observation _ (by omega)
  simp_rw [he]
  simp

theorem seed_camera_energy_not_summable :
    ¬ Summable (fun j : ℕ => ‖finiteMaterialObservation (Finsupp.single 1 (1 : ℂ)) (j+2)‖^2) := by
  rw [camera_energy_summable_iff _ (by simp)]
  simp [finiteTotal]

/-- Keeping the extracted total and every centered camera observation is
still an injective encoding of the SAME finite material data. -/
theorem total_and_centered_injective (a b : ℕ →₀ ℂ) (ha : a 0 = 0) (hb : b 0 = 0)
    (htotal : finiteTotal a = finiteTotal b)
    (hcentered : ∀ camera, 2 ≤ camera →
      finiteMaterialObservation a camera-finiteTotal a =
        finiteMaterialObservation b camera-finiteTotal b) : a = b := by
  apply all_cameras_finite_injective a b ha hb
  intro camera hc
  have h := hcentered camera hc
  rw [htotal] at h
  linear_combination h

/-- All ordered crosses survive the extraction of the common total. -/
theorem camera_polarized_total_split (a b : ℕ →₀ ℂ) (camera other : ℕ) :
    star (finiteMaterialObservation a camera)*finiteMaterialObservation b other =
      star (finiteTotal a)*finiteTotal b +
      star (finiteTotal a)*(finiteMaterialObservation b other-finiteTotal b) +
      star (finiteMaterialObservation a camera-finiteTotal a)*finiteTotal b +
      star (finiteMaterialObservation a camera-finiteTotal a)*
        (finiteMaterialObservation b other-finiteTotal b) := by
  simp only [star_sub]
  ring

/-- The literal uncompleted total of the prescribed source at zero phase.
This is a diagnostic of the proposed common-component extraction, not a
substitute for the completed response or its retained return. -/
def nativeTotalPrefix (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, (criticalMaterialSample 0 (n+1)).re

theorem native_total_square_lower (k : ℕ) (hk : 1 ≤ k) :
    (k : ℝ) ≤ nativeTotalPrefix (k^2) := by
  have hkp : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hsum : (∑ _n ∈ Finset.range (k^2), 1/(k : ℝ)) = k := by
    simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_pow]
    field_simp
  rw [← hsum]
  unfold nativeTotalPrefix
  apply Finset.sum_le_sum
  intro n hn
  have hnle : n+1 ≤ k^2 := by have := Finset.mem_range.mp hn; omega
  have hs : Real.sqrt ((n+1 : ℕ) : ℝ) ≤ (k : ℝ) := by
    calc
      _ ≤ Real.sqrt ((k^2 : ℕ) : ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast hnle)
      _ = _ := by rw [Nat.cast_pow,Real.sqrt_sq (Nat.cast_nonneg k)]
  have hspos : 0 < Real.sqrt ((n+1 : ℕ) : ℝ) := by positivity
  have h := one_div_le_one_div_of_le hspos hs
  simpa only [criticalMaterialSample,zero_mul,Complex.ofReal_zero,mul_zero,
    neg_zero,Complex.exp_zero,mul_one,Complex.ofReal_re,one_div] using h

/-- The native total cannot be retained as a finite global scalar by this
finite-data extraction. The completed source itself is not declared divergent. -/
theorem native_total_unbounded (C : ℝ) : ∃ N, C < nativeTotalPrefix N := by
  obtain ⟨k,hk⟩ := exists_nat_gt (max C 0+1)
  have hkp : (0 : ℝ) < k := by linarith [le_max_right C 0]
  have hkNat : 0 < k := by exact_mod_cast hkp
  exact ⟨k^2,lt_of_lt_of_le (by linarith [le_max_left C 0])
    (native_total_square_lower k (by omega))⟩

end
end CarryGlobalCameraBudget
