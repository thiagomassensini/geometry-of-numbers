# SourceProductRule Audit Report (2026-11-02)

## Scope
Closed publication audit for the algebraic formalization in `SourceProductRule.lean` on branch `agent/tfvd-uniform-relative-source`.

## Exact theorem statements (`#check`)

1. `CarrySourceBezout.sourceOperator_mul.{u_1} {R : Type u_1} [CommRing R] (oddSector : Bool) (H U : PowerSeries R) : sourceOperator oddSector (H * U) = U * sourceOperator oddSector H + H * sourceOperator oddSector U`

2. `CarrySourceBezout.bezout_mul_common.{u_1} {R : Type u_1} [CommRing R] [IsDomain R] (U A C : PowerSeries R) : bezout (U * A) (U * C) = left U * right U * bezout A C`

3. `CarrySourceBezout.sourceKernelSeries_product_rule.{u_1} {R : Type u_1} [CommRing R] [IsDomain R] (oddSector : Bool) (H U : PowerSeries R) : sourceKernelSeries oddSector (H * U) = left U * right U * sourceKernelSeries oddSector H + left H * right H * sourceKernelSeries oddSector U`

4. `CarrySourceBezout.coefficientBlock_sourceKernelSeries_product_rule.{u_1} {R : Type u_1} [CommRing R] [IsDomain R] (oddSector : Bool) (H U : PowerSeries R) (r : ℕ) : coefficientBlock (sourceKernelSeries oddSector (H * U)) r = coefficientBlock (left U * right U * sourceKernelSeries oddSector H) r + coefficientBlock (left H * right H * sourceKernelSeries oddSector U) r`

## Directed audit results

- Directed compile (`bash research/tfvd-uniform-relative-source/compile.sh SourceProductRule`): `RC_COMPILE=0`.
- Axiom audit (`#print axioms` over all four theorems): `RC_AUDIT=0`.
- `#print axioms` output (all four): depends on `[propext, Classical.choice, Quot.sound]`.
- `sorry` check (`rg -n "sorry" .../SourceProductRule.lean`): no matches (`RC_SORRY=1` from `rg` means "not found").
- Whitespace/conflict check (`git diff --check`): clean (`RC_DIFFCHECK=0`).

## External rational controls (exact, not yet formalized in Lean)

Recorded as external exact controls only (no additional Lean formalization in this publication):

- For `H = 1 - X + X^2/8`, sector `false`, `2x2` block determinant: `1/16`.
- For `C = 1 - X - X^2`, sector `false`, `2x2` block determinant: `-5`.
