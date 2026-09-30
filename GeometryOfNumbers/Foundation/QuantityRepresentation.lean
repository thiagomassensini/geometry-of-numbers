import Init

/-!
# Faithful quantity representation, before positional syntax

Constructive port of the elementary information-escape lemma from
`quantity-representation-foundations`, commit
`66f9ab46c6fa2622c5e6d9f5ed2c497040c62374`:
`QuantityRepresentationFoundations/InformationEscape.lean`.

No finiteness, recurrence, radix, digit, mass, or carry mechanism is assumed
or derived in this module. The source types remain arbitrary.
-/

namespace GeometryOfNumbers.Foundation

set_option autoImplicit false

universe u v w

/-- Distinguishable quantities remain distinguishable after encoding. -/
def FaithfulRepresentation {Q : Type u} {S : Type v} (encode : Q → S) : Prop :=
  ∀ ⦃a b : Q⦄, encode a = encode b → a = b

/-- Local agreement cannot erase distinction in a faithful split encoding. -/
theorem sameLocal_forces_extension_difference
    {Q : Type u} {Local : Type v} {Extension : Type w}
    (encode : Q → Local × Extension)
    (hfaithful : FaithfulRepresentation encode)
    {a b : Q} (hne : a ≠ b)
    (hlocal : (encode a).1 = (encode b).1) :
    (encode a).2 ≠ (encode b).2 := by
  intro hextension
  exact hne (hfaithful (Prod.ext hlocal hextension))

/-- A further change of faithful coordinates preserves faithfulness. -/
theorem faithfulRepresentation_comp
    {Q : Type u} {S : Type v} {T : Type w} (encode : Q → S) (change : S → T)
    (hencode : FaithfulRepresentation encode)
    (hchange : FaithfulRepresentation change) :
    FaithfulRepresentation (fun q => change (encode q)) := by
  intro a b h
  exact hencode (hchange h)

end GeometryOfNumbers.Foundation
