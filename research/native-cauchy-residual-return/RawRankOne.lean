import JetResidual
import ProjectionLoss
import Mathlib.LinearAlgebra.Matrix.Rank

namespace CarryCauchyResidual
open CarrySelfAdjointOperator ChiralReturn CarryReturnDeflation CarryPositiveSquare
open Filter Topology
open scoped InnerProductSpace ComplexConjugate BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000

/-- The untouched signed physical Cauchy kernel in the original source
coordinates. -/
def nativeRawKernel (k i j : ℕ) : ℂ :=
  cauchy k i j * (1 - star (sourceReturn k i) * sourceReturn k j)

/-- The raw finite form, before forming any jets or changing coefficients. -/
def nativeRawForm (k N : ℕ) (c d : Fin N → ℂ) : ℂ :=
  ∑ i : Fin N, ∑ j : Fin N,
    star (c i) * d j * nativeRawKernel k i.val j.val

theorem nativeBalance_basis_eq_nativeRawKernel (k N : ℕ) (i j : Fin N) :
    nativeBalance k N (Pi.single i 1) (Pi.single j 1) =
      nativeRawKernel k i.val j.val := by
  have hi : radialIncidentSynthesis k N (Pi.single i 1) = feature k i.val := by
    simp [radialIncidentSynthesis, feature]
  have hj : radialIncidentSynthesis k N (Pi.single j 1) = feature k j.val := by
    simp [radialIncidentSynthesis, feature]
  have hri : radialReturnedSynthesis k N (Pi.single i 1) =
      sourceReturn k i.val • feature k i.val := by
    rw [radialReturnedSynthesis_eq_incident_multiply]
    simp only [radialIncidentSynthesis, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Finset.sum_eq_single i]
    · simp [sourceReturn, feature]
    · intro b hb hbi
      simp [hbi]
    · simp
  have hrj : radialReturnedSynthesis k N (Pi.single j 1) =
      sourceReturn k j.val • feature k j.val := by
    rw [radialReturnedSynthesis_eq_incident_multiply]
    simp only [radialIncidentSynthesis, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Finset.sum_eq_single j]
    · simp [sourceReturn, feature]
    · intro b hb hbj
      simp [hbj]
    · simp
  rw [nativeBalance, balance, hi, hj, hri, hrj]
  simp only [inner_smul_left, inner_smul_right, feature_inner]
  unfold nativeRawKernel cauchy
  simp only [starRingEnd_apply]
  ring_nf

theorem nativeBalance_eq_nativeRawForm (k N : ℕ) (c d : Fin N → ℂ) :
    nativeBalance k N c d = nativeRawForm k N c d := by
  rw [nativeBalance, balance,
    radialReturnedSynthesis_eq_incident_multiply k N c,
    radialReturnedSynthesis_eq_incident_multiply k N d]
  simp only [radialIncidentSynthesis, LinearMap.coe_mk, AddHom.coe_mk,
    inner_sum, sum_inner, inner_smul_left, inner_smul_right]
  unfold nativeRawForm nativeRawKernel
  rw [← Finset.sum_sub_distrib]
  simp_rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [sourceReturn, feature_inner, cauchy]
  simp only [starRingEnd_apply, map_mul]
  ring_nf

theorem nativeRawKernel_tendsto (i j : ℕ) :
    Tendsto (fun k => nativeRawKernel k i j) atTop (nhds (4 *
      (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ))) := by
  let h₀ : ℂ := (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ)
  let αi : ℂ := 4*h₀*((i:ℂ)+1)
  let αj : ℂ := 4*h₀*((j:ℂ)+1)
  have hs : Tendsto (fun k => star ((sourceReturn k i+1)*radialScale k) +
      (sourceReturn k j+1)*radialScale k -
      star ((sourceReturn k i+1)*radialScale k)*(sourceReturn k j+1)) atTop
      (nhds (star αi + αj)) := by
    have hi := (source_tangent i).star
    have hj := source_tangent j
    have hq := (sourceReturn_tendsto j).add_const 1
    have hmul := hi.mul hq
    have hi' : Tendsto (fun k => star ((sourceReturn k i+1)*radialScale k)) atTop
        (nhds (star αi)) := by simpa [h₀, αi] using hi
    have hj' : Tendsto (fun k => (sourceReturn k j+1)*radialScale k) atTop
        (nhds αj) := by simpa [h₀, αj] using hj
    have hq' : Tendsto (fun k => sourceReturn k j+1) atTop (nhds (0:ℂ)) := by
      simpa using hq
    have hmul' : Tendsto (fun k => star ((sourceReturn k i+1)*radialScale k) *
        (sourceReturn k j+1)) atTop (nhds (star αi*0)) := by
      simpa using hi'.mul hq'
    simpa using (hi'.add hj').sub hmul'
  have hden : ((i:ℂ)+(j:ℂ)+2) ≠ 0 := by
    exact_mod_cast (show (i:ℝ)+(j:ℝ)+2 ≠ 0 by positivity)
  have hquot := hs.div_const ((i:ℂ)+(j:ℂ)+2)
  have hfactor (k : ℕ) : nativeRawKernel k i j =
      (star ((sourceReturn k i+1)*radialScale k) +
        (sourceReturn k j+1)*radialScale k -
        star ((sourceReturn k i+1)*radialScale k)*(sourceReturn k j+1)) /
        ((i:ℂ)+(j:ℂ)+2) := by
    unfold nativeRawKernel cauchy radialScale
    have hK : star ((sourceReturn k i+1)*((k:ℂ)+1)) =
        star (sourceReturn k i+1)*((k:ℂ)+1) := by simp
    have hsplit : 1-star (sourceReturn k i)*sourceReturn k j =
        star (sourceReturn k i+1) + (sourceReturn k j+1) -
          star (sourceReturn k i+1)*(sourceReturn k j+1) := by
      simp only [RCLike.star_def, map_add, map_one]
      ring_nf
    rw [hK, hsplit]
    field_simp [hden]
  have hlimit : (star αi + αj) / ((i:ℂ)+(j:ℂ)+2) = 4*h₀ := by
    simp [αi, αj, h₀]
    field_simp [hden]
    ring_nf
  rw [hlimit] at hquot
  exact hquot.congr' (Filter.Eventually.of_forall (fun k => (hfactor k).symm))

/-- Entrywise convergence of the complete fixed-size raw matrix. -/
theorem nativeRawForm_matrix_tendsto (N : ℕ) (i j : Fin N) :
    Tendsto (fun k => nativeRawKernel k i.val j.val) atTop
      (nhds (4*(canonicalCompletedNativeLogDerivativeMoment 0:ℂ))) :=
  nativeRawKernel_tendsto i.val j.val

/-- Fixed coefficient vectors retain only their total coefficient at the raw
scale. The coefficient vectors here are independent of k. -/
theorem nativeRawForm_tendsto (N : ℕ) (c d : Fin N → ℂ) :
    Tendsto (fun k => nativeRawForm k N c d) atTop
      (nhds (4*(canonicalCompletedNativeLogDerivativeMoment 0:ℂ) *
        star (∑ i, c i) * ∑ j, d j)) := by
  unfold nativeRawForm
  have hs : Tendsto (fun k => ∑ i : Fin N, ∑ j : Fin N,
      star (c i)*d j*nativeRawKernel k i.val j.val) atTop
        (nhds (∑ i : Fin N, ∑ j : Fin N,
        star (c i)*d j*(4*(canonicalCompletedNativeLogDerivativeMoment 0:ℂ)))) := by
    apply tendsto_finsetSum
    intro i _
    apply tendsto_finsetSum
    intro j _
    exact (nativeRawKernel_tendsto i.val j.val).const_mul (star (c i)*d j)
  have hsum : (∑ i : Fin N, ∑ j : Fin N,
      star (c i)*d j*(4*(canonicalCompletedNativeLogDerivativeMoment 0:ℂ))) =
      4*(canonicalCompletedNativeLogDerivativeMoment 0:ℂ) * star (∑ i, c i) * ∑ j, d j := by
    let H : ℂ := 4*(canonicalCompletedNativeLogDerivativeMoment 0:ℂ)
    calc
      _ = ∑ i : Fin N, (∑ j : Fin N, star (c i)*d j)*H := by
            apply Finset.sum_congr rfl
            intro i _
            calc
              _ = ∑ j : Fin N, (star (c i)*d j)*H := by
                    apply Finset.sum_congr rfl
                    intro j _
                    simp [H, mul_assoc]
              _ = _ := (Finset.sum_mul Finset.univ _ H).symm
      _ = (∑ i : Fin N, ∑ j : Fin N, star (c i)*d j)*H :=
            (Finset.sum_mul Finset.univ _ H).symm
      _ = ((∑ i : Fin N, star (c i)) * (∑ j : Fin N, d j))*H := by
            rw [← Finset.sum_mul_sum]
      _ = _ := by
            have hconj : (∑ i : Fin N, star (c i)) = star (∑ i : Fin N, c i) := by
              simpa only [starRingEnd_apply] using
                (map_sum (starRingEnd ℂ) c Finset.univ).symm
            rw [hconj]
            simp only [H]
            ring_nf
  rw [hsum] at hs
  exact hs

def nativeRawMatrix (k N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => nativeRawKernel k i.val j.val

def nativeRawLimitMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  fun _ _ => 4*(canonicalCompletedNativeLogDerivativeMoment 0:ℂ)

theorem nativeRawMatrix_entrywise_tendsto (N : ℕ) (i j : Fin N) :
    Tendsto (fun k => nativeRawMatrix k N i j) atTop
      (nhds (nativeRawLimitMatrix N i j)) := by
  exact nativeRawForm_matrix_tendsto N i j

def nativeRawLimitOperator (N : ℕ) : (Fin N → ℂ) →ₗ[ℂ] (Fin N → ℂ) where
  toFun c := fun _ => 4*(canonicalCompletedNativeLogDerivativeMoment 0:ℂ)*∑ i, c i
  map_add' c d := by
    funext i
    simp [Pi.add_apply, Finset.sum_add_distrib, mul_add]
  map_smul' a c := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    ring_nf

theorem nativeRawLimitMatrix_mulVec (N : ℕ) (c : Fin N → ℂ) :
    Matrix.mulVec (nativeRawLimitMatrix N) c = nativeRawLimitOperator N c := by
  change (fun i : Fin N => ∑ j : Fin N,
      4*(canonicalCompletedNativeLogDerivativeMoment 0:ℂ)*c j) = _
  funext i
  change (∑ j : Fin N,
      4*(canonicalCompletedNativeLogDerivativeMoment 0:ℂ)*c j) =
        4*(canonicalCompletedNativeLogDerivativeMoment 0:ℂ)*∑ j : Fin N, c j
  exact (Finset.mul_sum Finset.univ c
    (4*(canonicalCompletedNativeLogDerivativeMoment 0:ℂ))).symm

theorem nativeRawLimitOperator_apply (N : ℕ) (c : Fin N → ℂ) :
    nativeRawLimitOperator N c =
      (4*(canonicalCompletedNativeLogDerivativeMoment 0:ℂ)*∑ i, c i) •
        (fun _ : Fin N => (1:ℂ)) := by
  funext i
  simp only [nativeRawLimitOperator, LinearMap.coe_mk, AddHom.coe_mk,
    Pi.smul_apply, smul_eq_mul]
  ring_nf

theorem nativeRawLimitOperator_kernel_iff (N : ℕ) (hN : 0 < N) (c : Fin N → ℂ) :
    nativeRawLimitOperator N c = 0 ↔ ∑ i, c i = 0 := by
  rw [nativeRawLimitOperator_apply]
  constructor
  · intro h
    change (4*(canonicalCompletedNativeLogDerivativeMoment 0:ℂ)*∑ i, c i) •
      (fun _ : Fin N => (1:ℂ)) = 0 at h
    have hv := congrArg (fun f : Fin N → ℂ => f (⟨0,hN⟩ : Fin N)) h
    have hcoef : 4*(canonicalCompletedNativeLogDerivativeMoment 0:ℂ)*∑ i, c i = 0 := by
      simpa [Pi.smul_apply, smul_eq_mul] using hv
    have h0 : (4:ℂ)*(canonicalCompletedNativeLogDerivativeMoment 0:ℂ) ≠ 0 := by
      apply mul_ne_zero (by norm_num)
      exact_mod_cast canonicalCompletedNativeLogDerivativeMoment_zero_pos.ne'
    exact (mul_eq_zero.mp hcoef).resolve_left h0
  · intro h
    ext i
    simp [h, Pi.smul_apply, smul_eq_mul]

theorem nativeRawLimitMatrix_rank_one (N : ℕ) (hN : 0 < N) :
    (nativeRawLimitMatrix N).rank = 1 := by
  classical
  have h0 : (4:ℂ)*(canonicalCompletedNativeLogDerivativeMoment 0:ℂ) ≠ 0 := by
    apply mul_ne_zero (by norm_num)
    exact_mod_cast canonicalCompletedNativeLogDerivativeMoment_zero_pos.ne'
  have hvec : (fun _ : Fin N => (4:ℂ)*
      (canonicalCompletedNativeLogDerivativeMoment 0:ℂ)) ≠ 0 := by
    intro hz
    have hv := congrFun hz (⟨0,hN⟩ : Fin N)
    exact h0 (by simpa using hv)
  have hcols : Set.range (nativeRawLimitMatrix N).col =
      {fun _ : Fin N => (4:ℂ)*(canonicalCompletedNativeLogDerivativeMoment 0:ℂ)} := by
    ext v
    constructor
    · rintro ⟨j,hj⟩
      rw [Set.mem_singleton_iff]
      funext i
      simpa [nativeRawLimitMatrix, Matrix.col] using (congrFun hj i).symm
    · intro hv
      rw [Set.mem_singleton_iff] at hv
      subst v
      refine ⟨⟨0,hN⟩, ?_⟩
      funext i
      simp [nativeRawLimitMatrix, Matrix.col]
  rw [Matrix.rank_eq_finrank_span_cols, hcols]
  exact finrank_span_singleton hvec

def nativeRawHead (N : ℕ) : Fin (N+1) → ℂ := Pi.single 0 1

def nativeRawSchurForm (k N : ℕ) (c d : Fin (N+1) → ℂ) : ℂ :=
  nativeRawForm k (N+1) c d -
    star (nativeRawForm k (N+1) (nativeRawHead N) c) *
      nativeRawForm k (N+1) (nativeRawHead N) d /
      nativeRawForm k (N+1) (nativeRawHead N) (nativeRawHead N)

theorem nativeRawHead_sum (N : ℕ) : ∑ i : Fin (N+1), nativeRawHead N i = 1 := by
  simp [nativeRawHead]

theorem nativeRawForm_headCross_eq_anchorCross (k N : ℕ) (c : Fin (N+1) → ℂ) :
    nativeRawForm k (N+1) (nativeRawHead N) c =
      anchorCross (oneReturn k) (nativeAnchor k)
        (radialIncidentSynthesis k (N+1) c) (radialReturnedSynthesis k (N+1) c) := by
  rw [← nativeBalance_eq_nativeRawForm]
  change nativeBalance k (N+1) (Pi.single 0 1) c = _
  unfold nativeBalance
  rw [native_incident_head, native_returned_head]
  exact (anchorCross_eq_balance (oneReturn k) (nativeAnchor k)
    (radialIncidentSynthesis k (N+1) c) (radialReturnedSynthesis k (N+1) c)).symm

theorem nativeRawForm_headHead_eq (k N : ℕ) :
    nativeRawForm k (N+1) (nativeRawHead N) (nativeRawHead N) =
      (oneDeficit k:ℂ)*(anchorMass k:ℂ) := by
  rw [← nativeBalance_eq_nativeRawForm]
  change nativeBalance k (N+1) (Pi.single 0 1) (Pi.single 0 1) = _
  rw [nativeBalance_basis_eq_nativeRawKernel]
  have hdef : 1-star (oneReturn k)*oneReturn k = (oneDeficit k:ℂ) := by
    simpa only [deficit, starRingEnd_apply] using native_deficit k
  have hhead : sourceReturn k 0 = oneReturn k := by rfl
  rw [nativeRawKernel, cauchy]
  simp only [Fin.val_zero]
  rw [hhead, hdef]
  simp only [Nat.cast_zero, zero_add, anchorMass]
  have hk : (2:ℂ) ≠ 0 := by norm_num
  simp only [Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_natCast,
    Complex.ofReal_ofNat, Complex.ofReal_one]
  field_simp [hk]

/-- The first Schur subtraction of the raw finite form is the exact physical
remainder already defined by the orthogonal projection onto the first source. -/
theorem nativeRawSchurForm_eq_remainingPair (k N : ℕ) (c d : Fin (N+1) → ℂ)
    (hd : oneDeficit k ≠ 0) :
    nativeRawSchurForm k N c d = remainingPair k (N+1) c d/(oneDeficit k:ℂ) := by
  rw [nativeRawSchurForm, ← nativeBalance_eq_nativeRawForm,
    nativeRawForm_headCross_eq_anchorCross, nativeRawForm_headCross_eq_anchorCross,
    nativeRawForm_headHead_eq]
  exact (native_schur_remainder k (N+1) c d hd).symm

theorem nativeRawSchurForm_tendsto_zero (N : ℕ) (c d : Fin (N+1) → ℂ) :
    Tendsto (fun k => nativeRawSchurForm k N c d) atTop (nhds 0) := by
  let H : ℂ := 4*(canonicalCompletedNativeLogDerivativeMoment 0:ℂ)
  have hs := nativeRawForm_tendsto (N+1) c d
  have hx₀ := nativeRawForm_tendsto (N+1) (nativeRawHead N) c
  have hy₀ := nativeRawForm_tendsto (N+1) (nativeRawHead N) d
  have hh₀ := nativeRawForm_tendsto (N+1) (nativeRawHead N) (nativeRawHead N)
  have hx : Tendsto (fun k => nativeRawForm k (N+1) (nativeRawHead N) c) atTop
      (nhds (H*∑ i : Fin (N+1), c i)) := by
    simpa [H, nativeRawHead_sum] using hx₀
  have hy : Tendsto (fun k => nativeRawForm k (N+1) (nativeRawHead N) d) atTop
      (nhds (H*∑ i : Fin (N+1), d i)) := by
    simpa [H, nativeRawHead_sum] using hy₀
  have hh : Tendsto (fun k => nativeRawForm k (N+1) (nativeRawHead N)
      (nativeRawHead N)) atTop (nhds H) := by
    simpa [H, nativeRawHead_sum] using hh₀
  have hH : H ≠ 0 := by
    apply mul_ne_zero (by norm_num)
    exact_mod_cast canonicalCompletedNativeLogDerivativeMoment_zero_pos.ne'
  have hHstar : star H = H := by simp [H]
  have hcancel : H*star (∑ i : Fin (N+1), c i)*∑ j : Fin (N+1), d j -
      star (H*∑ i : Fin (N+1), c i)*(H*∑ j : Fin (N+1), d j)/H = 0 := by
    rw [star_mul, hHstar]
    field_simp [hH]
    ring_nf
  have ht := hs.sub (((continuous_star.tendsto _).comp hx).mul hy |>.div hh hH)
  change Tendsto (fun k => nativeRawForm k (N+1) c d -
      star (nativeRawForm k (N+1) (nativeRawHead N) c) *
        nativeRawForm k (N+1) (nativeRawHead N) d /
        nativeRawForm k (N+1) (nativeRawHead N) (nativeRawHead N)) atTop
    (nhds (H*star (∑ i : Fin (N+1), c i)*∑ j : Fin (N+1), d j -
      star (H*∑ i : Fin (N+1), c i)*(H*∑ j : Fin (N+1), d j)/H)) at ht
  rw [hcancel] at ht
  exact ht

/-- For the original, k-dependent full jet input, the same raw Schur form is
exactly the existing physical jet remainder. -/
theorem nativeRawJetSchur_eq_jetSchurRemainder_eventually (n : ℕ)
    (x y : Fin (2*(n+1)) → ℂ) :
    ∀ᶠ k : ℕ in atTop, nativeRawSchurForm k (2*n+1)
      (nativeSourceChiralJetInput (n+1) k x)
      (nativeSourceChiralJetInput (n+1) k y) = jetSchurRemainder (n+1) k x y := by
  filter_upwards [oneDeficit_eventually_pos] with k hk
  have he := nativeRawSchurForm_eq_remainingPair k (2*n+1)
    (nativeSourceChiralJetInput (n+1) k x)
    (nativeSourceChiralJetInput (n+1) k y) (ne_of_gt hk)
  unfold jetSchurRemainder jetRemainingPair
  convert he using 1
  congr 1

theorem nativeRawJetSchur_tendsto_canonical (n : ℕ)
    (x y : Fin (2*(n+1)) → ℂ) :
    Tendsto (fun k => nativeRawSchurForm k (2*n+1)
      (nativeSourceChiralJetInput (n+1) k x)
      (nativeSourceChiralJetInput (n+1) k y)) atTop
      (nhds (2*(canonicalBoundaryPair (n+1) x y -
        conj (canonicalBoundaryPair (n+1) (headBoundary n) x)*
          canonicalBoundaryPair (n+1) (headBoundary n) y/
          (canonicalCompletedNativeLogDerivativeMoment 0:ℂ)))) := by
  exact (jet_remaining_schur_tendsto n x y).congr'
    (Filter.EventuallyEq.symm (nativeRawJetSchur_eq_jetSchurRemainder_eventually n x y))

/-- Regression guard: the known loss from projecting the returned channel is
kept verbatim, including its nonzero second-source limit. -/
theorem nativeProjectionLoss_regression :
    (∀ k N c d, projectedBothPair k N c d = remainingPair k N c d +
      inner ℂ (returnedHead k N c) (returnedHead k N d)) ∧
      Tendsto (fun k => ‖returnedHead k 2 (Pi.single 1 1)‖^2/oneDeficit k) atTop
        (nhds (4*canonicalCompletedNativeLogDerivativeMoment 0/9)) := by
  exact ⟨fun k N c d => projection_loss_polarized k N c d,
    second_source_projection_loss⟩

end
end CarryCauchyResidual
