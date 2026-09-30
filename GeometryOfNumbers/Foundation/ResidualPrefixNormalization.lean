import GeometryOfNumbers.Foundation.ResidualTowerCapacity

/-!
# Label-neutral counting normalization of a resolved prefix

Capacity alone does not imply uniformity of arbitrary weights. The additional
principle here is explicit: a counting normalization is invariant under every
relabeling of the resolved states, without retaining a distinguished state.
This is NOT a claim that every permutation preserves the dynamics or values.

Transpositions force equal weights. Finite addition then determines the formal
unit share by cross multiplication. No quotient, measure, real number, or
metric is used. A common-denominator natural weight assignment is sufficient
for this combinatorial layer; arbitrary numerical measures are not covered.
-/

namespace GeometryOfNumbers.Foundation

set_option autoImplicit false
universe u v

/-- Reversible changes of labels, with both inverse laws supplied as data. -/
structure StateRelabeling (State : Type u) where
  forward : State → State
  backward : State → State
  backward_forward : ∀ x, backward (forward x) = x
  forward_backward : ∀ x, forward (backward x) = x

/-- Additional neutrality principle for an assignment on the bare state set.
This is stronger than covariance of a state-dependent assignment under renaming. -/
def RelabelingInvariant {State : Type u} {Weight : Type v}
    (weight : State → Weight) : Prop :=
  ∀ labels : StateRelabeling State, ∀ x, weight (labels.forward x) = weight x

private def swapFiniteLabels {N : Nat} (a b x : Fin N) : Fin N :=
  if x = a then b else if x = b then a else x

private theorem swapFiniteLabels_at_left {N : Nat} (a b : Fin N) :
    swapFiniteLabels a b a = b := by
  unfold swapFiniteLabels
  rw [if_pos rfl]

private theorem swapFiniteLabels_twice {N : Nat} (a b x : Fin N) :
    swapFiniteLabels a b (swapFiniteLabels a b x) = x := by
  by_cases ha : x = a
  · subst x
    rw [swapFiniteLabels_at_left]
    by_cases hba : b = a
    · subst b
      exact swapFiniteLabels_at_left a a
    · unfold swapFiniteLabels
      rw [if_neg hba, if_pos rfl]
  · by_cases hb : x = b
    · subst x
      unfold swapFiniteLabels
      rw [if_neg ha, if_pos rfl, if_pos rfl]
    · unfold swapFiniteLabels
      rw [if_neg ha, if_neg hb, if_neg ha, if_neg hb]

/-- A concrete transposition; no enumeration is chosen classically. -/
def finiteLabelTransposition {N : Nat} (a b : Fin N) : StateRelabeling (Fin N) where
  forward := swapFiniteLabels a b
  backward := swapFiniteLabels a b
  backward_forward := swapFiniteLabels_twice a b
  forward_backward := swapFiniteLabels_twice a b

/-- Transport the already constructed finite coding back to prefix states. -/
def residualPrefixRelabeling (b depth : Nat) (hb : 0 < b)
    (labels : StateRelabeling (Fin (b ^ depth))) :
    StateRelabeling (ResidualPrefix b depth) where
  forward := fun x => residualPrefixDecode b depth hb
    (labels.forward (residualPrefixEncode b depth x))
  backward := fun x => residualPrefixDecode b depth hb
    (labels.backward (residualPrefixEncode b depth x))
  backward_forward := by
    intro x
    rw [residualPrefix_encode_decode, labels.backward_forward,
      residualPrefix_decode_encode]
  forward_backward := by
    intro x
    rw [residualPrefix_encode_decode, labels.forward_backward,
      residualPrefix_decode_encode]

/-- Existence of transpositions, not a constant-weight field, proves uniformity. -/
theorem finiteLabel_relabelingInvariant_iff_constant {N : Nat} {Weight : Type v}
    (weight : Fin N → Weight) :
    RelabelingInvariant weight ↔ ∀ a b, weight a = weight b := by
  constructor
  · intro hinvariant a b
    have h := hinvariant (finiteLabelTransposition a b) a
    change weight (swapFiniteLabels a b a) = weight a at h
    rw [swapFiniteLabels_at_left] at h
    exact h.symm
  · intro hequal labels x
    exact hequal (labels.forward x) x

/-- The same neutrality theorem on the actual prefix, not just its codes. -/
theorem residualPrefix_relabelingInvariant_iff_constant
    (b depth : Nat) (hb : 0 < b) {Weight : Type v}
    (weight : ResidualPrefix b depth → Weight) :
    RelabelingInvariant weight ↔ ∀ a c, weight a = weight c := by
  constructor
  · intro hinvariant a c
    have h := hinvariant (residualPrefixRelabeling b depth hb
      (finiteLabelTransposition (residualPrefixEncode b depth a)
        (residualPrefixEncode b depth c))) a
    change weight (residualPrefixDecode b depth hb
      (swapFiniteLabels (residualPrefixEncode b depth a)
        (residualPrefixEncode b depth c) (residualPrefixEncode b depth a))) = weight a at h
    rw [swapFiniteLabels_at_left, residualPrefix_decode_encode] at h
    exact h.symm
  · intro hequal labels x
    exact hequal (labels.forward x) x

/-- Add counts on a finite list of labels; no cardinality or division API. -/
def finiteLabelTotal : (N : Nat) → (Fin N → Nat) → Nat
  | 0, _ => 0
  | N + 1, weight => weight ⟨0, Nat.zero_lt_succ N⟩ +
      finiteLabelTotal N (fun i => weight i.succ)

/-- Equal counts accumulate to capacity times the common count. -/
theorem finiteLabelTotal_of_equal (N c : Nat) (weight : Fin N → Nat)
    (hequal : ∀ i, weight i = c) : finiteLabelTotal N weight = N * c := by
  induction N with
  | zero => exact (Nat.zero_mul c).symm
  | succ N ih =>
    change weight ⟨0, Nat.zero_lt_succ N⟩ +
      finiteLabelTotal N (fun i => weight i.succ) = (N + 1) * c
    rw [hequal, ih (fun i => weight i.succ) (fun i => hequal i.succ),
      Nat.succ_mul, Nat.add_comm c]

/-- Unit counting obtains the total from finite addition, before normalization. -/
theorem finiteLabelTotal_unit (N : Nat) :
    finiteLabelTotal N (fun _ => 1) = N :=
  (finiteLabelTotal_of_equal N 1 (fun _ => 1) (fun _ => rfl)).trans (Nat.mul_one N)

/-- Capacity by itself permits nonuniform assignments, even with positive total. -/
theorem finiteCapacity_does_not_force_uniformity :
    ∃ weight : Fin 2 → Nat, finiteLabelTotal 2 weight = 1 ∧
      ¬ RelabelingInvariant weight := by
  refine ⟨fun i => if i.val = 0 then 1 else 0, rfl, ?_⟩
  intro hinvariant
  have h := (finiteLabel_relabelingInvariant_iff_constant _).1 hinvariant
    ⟨0, by decide⟩ ⟨1, by decide⟩
  exact Nat.zero_ne_one h.symm

/-- A formal share is data, not a rational quotient or a measure. -/
structure FormalCountingShare where
  numerator : Nat
  denominator : Nat
  denominator_positive : 0 < denominator

/-- Compare formal shares by cross multiplication, without reducing fractions. -/
def SameCountingShare (left right : FormalCountingShare) : Prop :=
  left.numerator * right.denominator = right.numerator * left.denominator

/-- Neutrality plus total normalization forces the unit-per-capacity relation.
The total is a separate premise; invariance does not specify a scale. -/
theorem finiteLabel_normalization_forces_unitShare (N D : Nat)
    (weight : Fin N → Nat) (hinvariant : RelabelingInvariant weight)
    (hnormalized : finiteLabelTotal N weight = D) (i : Fin N) :
    weight i * N = D := by
  have hequal := (finiteLabel_relabelingInvariant_iff_constant weight).1 hinvariant
  exact (Nat.mul_comm (weight i) N).trans
    ((finiteLabelTotal_of_equal N (weight i) weight (fun j => hequal j i)).symm.trans
      hnormalized)

/-- Formal unit normalization is unique as a share, not as numerator/denominator data. -/
theorem finiteLabel_normalizedShare_unique (N D : Nat) (hN : 0 < N) (hD : 0 < D)
    (weight : Fin N → Nat) (hinvariant : RelabelingInvariant weight)
    (hnormalized : finiteLabelTotal N weight = D) (i : Fin N) :
    SameCountingShare ⟨weight i, D, hD⟩ ⟨1, N, hN⟩ := by
  change weight i * N = 1 * D
  rw [Nat.one_mul]
  exact finiteLabel_normalization_forces_unitShare N D weight hinvariant hnormalized i

/-- The denominator is obtained by totaling unit counts on the proved prefix codes. -/
def canonicalResidualPrefixCountingShare (b depth : Nat) (hb : 0 < b)
    (_resolved : ResidualPrefix b depth) : FormalCountingShare where
  numerator := 1
  denominator := finiteLabelTotal (b ^ depth) (fun _ => 1)
  denominator_positive := by
    rw [finiteLabelTotal_unit]
    exact Nat.pow_pos hb

/-- No prefix receives a different share under any relabeling. -/
theorem canonicalResidualPrefixCountingShare_invariant (b depth : Nat) (hb : 0 < b) :
    RelabelingInvariant (canonicalResidualPrefixCountingShare b depth hb) := by
  intro labels x
  rfl

/-- Only after totaling the derived finite capacity do we identify `(1,b^depth)`. -/
theorem canonicalResidualPrefixCountingShare_eq_unit_over_capacity
    (b depth : Nat) (hb : 0 < b) (resolved : ResidualPrefix b depth) :
    (canonicalResidualPrefixCountingShare b depth hb resolved).numerator = 1 ∧
      (canonicalResidualPrefixCountingShare b depth hb resolved).denominator = b ^ depth :=
  ⟨rfl, finiteLabelTotal_unit (b ^ depth)⟩

/-- Any neutral natural-count normalization on the prefix realizes the same share.
Normalization is computed over the actual prefix through its proved decoder. -/
theorem residualPrefix_normalizedShare_unique (b depth D : Nat)
    (hb : 0 < b) (hD : 0 < D) (weight : ResidualPrefix b depth → Nat)
    (hinvariant : RelabelingInvariant weight)
    (hnormalized : finiteLabelTotal (b ^ depth)
      (fun i => weight (residualPrefixDecode b depth hb i)) = D)
    (resolved : ResidualPrefix b depth) :
    SameCountingShare ⟨weight resolved, D, hD⟩
      (canonicalResidualPrefixCountingShare b depth hb resolved) := by
  have hequal := (residualPrefix_relabelingInvariant_iff_constant b depth hb weight).1
    hinvariant
  have htotal := finiteLabelTotal_of_equal (b ^ depth) (weight resolved)
    (fun i => weight (residualPrefixDecode b depth hb i)) (fun i => hequal _ resolved)
  change weight resolved * finiteLabelTotal (b ^ depth) (fun _ => 1) = 1 * D
  rw [finiteLabelTotal_unit, Nat.one_mul, Nat.mul_comm (weight resolved)]
  exact htotal.symm.trans hnormalized

end GeometryOfNumbers.Foundation
