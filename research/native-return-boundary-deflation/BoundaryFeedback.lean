import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Tactic

namespace CarryReturnDeflation
open scoped InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Bookkeeping of two ORIGINAL channels, not a replacement Hilbert metric. -/
def balance (x rx y ry : E) : ℂ := inner ℂ x y - inner ℂ rx ry
def deficit (r : ℂ) : ℂ := 1 - conj r * r
def feedbackIn (r : ℂ) (x rx : E) : E := x - conj r • rx
def feedbackOut (r : ℂ) (x rx : E) : E := rx - r • x

/-- Exact two-channel feedback before any projection or scalar observation.
No contraction or sign premise is used. -/
theorem feedback_balance (r : ℂ) (x rx y ry : E) :
    deficit r * balance x rx y ry =
      inner ℂ (feedbackIn r x rx) (feedbackIn r y ry) -
        inner ℂ (feedbackOut r x rx) (feedbackOut r y ry) := by
  simp only [feedbackIn, feedbackOut, balance, deficit,
    inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    Complex.conj_conj]
  ring

/-- Polarized Bessel identity; BOTH independent input vectors are retained. -/
theorem projection_split (K : Submodule ℂ E) [K.HasOrthogonalProjection] (x y : E) :
    inner ℂ x y = inner ℂ (K.starProjection x) (K.starProjection y) +
      inner ℂ (x-K.starProjection x) (y-K.starProjection y) := by
  have hxy := K.starProjection_inner_eq_zero x (K.starProjection y)
    (K.starProjection_apply_mem y)
  have hyx := K.starProjection_inner_eq_zero y (K.starProjection x)
    (K.starProjection_apply_mem x)
  have hyx' := congrArg (fun z : ℂ => conj z) hyx
  simp only [map_zero, inner_conj_symm] at hyx'
  simp only [inner_sub_left, inner_sub_right] at hxy hyx' ⊢
  linear_combination hxy + hyx'

/-- Complete energy decomposition: a genuine projected channel plus the
TWO remaining channels. The latter are not assumed to have a sign. -/
theorem feedback_projection_split (K : Submodule ℂ E) [K.HasOrthogonalProjection]
    (r : ℂ) (x rx y ry : E) :
    deficit r * balance x rx y ry =
      inner ℂ (K.starProjection (feedbackIn r x rx))
        (K.starProjection (feedbackIn r y ry)) +
      (inner ℂ (feedbackIn r x rx-K.starProjection (feedbackIn r x rx))
        (feedbackIn r y ry-K.starProjection (feedbackIn r y ry)) -
        inner ℂ (feedbackOut r x rx) (feedbackOut r y ry)) := by
  rw [feedback_balance, projection_split K (feedbackIn r x rx) (feedbackIn r y ry)]
  ring

theorem feedback_anchor_in (r : ℂ) (e : E) :
    feedbackIn r e (r • e) = deficit r • e := by
  simp only [feedbackIn, deficit, smul_smul, sub_smul, one_smul]

theorem feedback_anchor_out (r : ℂ) (e : E) :
    feedbackOut r e (r • e) = 0 := by simp [feedbackOut]

/-- The full pair is retained: feedback has an exact inverse whenever its
original anchor deficit is nonzero. This vector identity precedes energies. -/
theorem feedback_reconstruct_incident (r : ℂ) (x rx : E) :
    deficit r • x = feedbackIn r x rx + conj r • feedbackOut r x rx := by
  simp only [deficit, feedbackIn, feedbackOut, smul_sub, smul_smul, sub_smul, one_smul]
  abel

theorem feedback_reconstruct_returned (r : ℂ) (x rx : E) :
    deficit r • rx = feedbackOut r x rx + r • feedbackIn r x rx := by
  simp only [deficit, feedbackIn, feedbackOut, smul_sub, smul_smul, sub_smul, one_smul]
  rw [mul_comm r (conj r)]
  abel

/-- Keeping the projected channel AND its complement reconstructs the
original incident vector. No invisible component is quotiented away. -/
theorem projected_reconstruct_incident (K : Submodule ℂ E) [K.HasOrthogonalProjection]
    (r : ℂ) (x rx : E) :
    deficit r • x = K.starProjection (feedbackIn r x rx) +
      (feedbackIn r x rx-K.starProjection (feedbackIn r x rx)) +
      conj r • feedbackOut r x rx := by
  rw [add_sub_cancel, feedback_reconstruct_incident]

theorem feedback_anchor_complement (K : Submodule ℂ E) [K.HasOrthogonalProjection]
    (r : ℂ) (e : E) (he : e ∈ K) :
    feedbackIn r e (r • e)-K.starProjection (feedbackIn r e (r • e))=0 := by
  rw [feedback_anchor_in, map_smul, K.starProjection_eq_self_iff.mpr he, sub_self]

/-- Explicit formula for the projection onto a pre-existing physical vector.
t is its ORIGINAL norm squared; no target Gram is used to select it. -/
theorem singleton_projection (e x : E) (t : ℝ) (ht : t ≠ 0)
    (he : inner ℂ e e = (t:ℂ)) :
    (Submodule.span ℂ ({e} : Set E)).starProjection x =
      ((t:ℂ)⁻¹ * inner ℂ e x) • e := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · apply Submodule.smul_mem
    exact Submodule.subset_span (by simp)
  · intro w hw
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hw
    rw [← ha]
    simp only [inner_smul_right, inner_sub_left, inner_smul_left, map_mul,
      map_inv₀, Complex.conj_ofReal, he]
    rw [inner_conj_symm x e]
    have ht' : (t:ℂ) ≠ 0 := by exact_mod_cast ht
    field_simp [ht']
    ring

theorem singleton_projection_pair (e x y : E) (t : ℝ) (ht : t ≠ 0)
    (he : inner ℂ e e = (t:ℂ)) :
    inner ℂ ((Submodule.span ℂ ({e}:Set E)).starProjection x)
      ((Submodule.span ℂ ({e}:Set E)).starProjection y) =
      conj (inner ℂ e x) * inner ℂ e y / (t:ℂ) := by
  rw [singleton_projection e x t ht he, singleton_projection e y t ht he,
    inner_smul_left, inner_smul_right, he]
  simp only [map_mul, map_inv₀, Complex.conj_ofReal]
  have ht' : (t:ℂ) ≠ 0 := by exact_mod_cast ht
  field_simp [ht']

def anchorCross (r : ℂ) (e x rx : E) : ℂ :=
  inner ℂ e x - conj r * inner ℂ e rx

theorem anchorCross_eq_balance (r : ℂ) (e x rx : E) :
    anchorCross r e x rx = balance e (r • e) x rx := by
  simp [anchorCross, balance, inner_smul_left]

theorem feedback_anchor_pair (r : ℂ) (e x rx : E) :
    inner ℂ e (feedbackIn r x rx) = anchorCross r e x rx := by
  simp only [feedbackIn, anchorCross, inner_sub_right, inner_smul_right]

/-- The projected term is exactly the Schur numerator of the ORIGINAL
signed balance, not a fitted norm or a squared defect. -/
theorem projected_feedback_pair (e x rx y ry : E) (r : ℂ) (t : ℝ)
    (ht : t ≠ 0) (he : inner ℂ e e = (t:ℂ)) :
    inner ℂ ((Submodule.span ℂ ({e}:Set E)).starProjection (feedbackIn r x rx))
      ((Submodule.span ℂ ({e}:Set E)).starProjection (feedbackIn r y ry)) =
      conj (anchorCross r e x rx) * anchorCross r e y ry / (t:ℂ) := by
  rw [singleton_projection_pair e _ _ t ht he, feedback_anchor_pair, feedback_anchor_pair]

/-- The two-channel complement is the original Schur remainder, with its
exact source scalar. Only nonzero denominators are needed, never positivity. -/
theorem physical_schur_remainder (e x rx y ry : E) (r : ℂ) (t : ℝ)
    (ht : t ≠ 0) (he : inner ℂ e e = (t:ℂ)) (hd : deficit r ≠ 0) :
    let P := (Submodule.span ℂ ({e}:Set E)).starProjection
    (inner ℂ (feedbackIn r x rx-P (feedbackIn r x rx))
      (feedbackIn r y ry-P (feedbackIn r y ry)) -
      inner ℂ (feedbackOut r x rx) (feedbackOut r y ry)) / deficit r =
      balance x rx y ry -
        conj (anchorCross r e x rx)*anchorCross r e y ry/(deficit r*(t:ℂ)) := by
  dsimp only
  have hs := feedback_projection_split (Submodule.span ℂ ({e}:Set E)) r x rx y ry
  rw [projected_feedback_pair e x rx y ry r t ht he] at hs
  have ht' : (t:ℂ) ≠ 0 := by exact_mod_cast ht
  field_simp [hd, ht'] at hs ⊢
  linear_combination -hs

def eraseHead {N : ℕ} (c : Fin (N+1) → ℂ) : Fin (N+1) → ℂ :=
  fun i => if i=0 then 0 else c i

theorem source_head_decomposition {N : ℕ} (c : Fin (N+1) → ℂ) :
    c = c 0 • Pi.single 0 1 + eraseHead c := by
  funext i
  by_cases hi : i=0
  · subst i; simp [eraseHead]
  · simp [eraseHead,hi]

theorem linearMap_eraseHead {N : ℕ} (L : (Fin (N+1) → ℂ) →ₗ[ℂ] E)
    (hh : L (Pi.single 0 1)=0) (c : Fin (N+1) → ℂ) : L c = L (eraseHead c) := by
  conv_lhs => rw [source_head_decomposition c]
  rw [map_add,map_smul,hh,smul_zero,zero_add]

/-- Scaling the old anchor by its own source amplitude changes neither
Schur subtraction nor its physical complement. No fitted normalization. -/
theorem scaled_anchor_schur (e x rx y ry : E) (r a : ℂ) (t : ℝ)
    (ht : t ≠ 0) (he : inner ℂ e e = (t:ℂ))
    (hd : deficit r ≠ 0) (ha : a ≠ 0) :
    conj (balance (a • e) (a • (r • e)) x rx) *
      balance (a • e) (a • (r • e)) y ry /
        balance (a • e) (a • (r • e)) (a • e) (a • (r • e)) =
      conj (anchorCross r e x rx)*anchorCross r e y ry/(deficit r*(t:ℂ)) := by
  have hc : conj a ≠ 0 := by intro h; apply ha; simpa using congrArg (fun z : ℂ => conj z) h
  have ht' : (t:ℂ) ≠ 0 := by exact_mod_cast ht
  have haSelf : balance (a • e) (a • (r • e)) (a • e) (a • (r • e)) =
      conj a*a*deficit r*(t:ℂ) := by
    simp only [balance, inner_smul_left, inner_smul_right, he]
    unfold deficit
    ring
  rw [haSelf]
  have hx : balance (a • e) (a • (r • e)) x rx = conj a * anchorCross r e x rx := by
    simp only [balance, anchorCross, inner_smul_left]
    ring
  have hy : balance (a • e) (a • (r • e)) y ry = conj a * anchorCross r e y ry := by
    simp only [balance, anchorCross, inner_smul_left]
    ring
  rw [hx,hy]
  simp only [map_mul, Complex.conj_conj]
  field_simp

end
end CarryReturnDeflation
