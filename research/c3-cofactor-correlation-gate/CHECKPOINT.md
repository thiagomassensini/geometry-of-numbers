# Checkpoint — correlated C3 coefficient gate

- Phase: source normalization; branch `agent/c3-cofactor-correlation-gate-20261112`, base PR #322 merge `de8f044d78260fd4ba9f728c3bb313adfa0255df`.
- Latest checkpoint commit: pending; base `40d30d6 docs(c3): checkpoint correlated coefficient enclosure`.
- Files added: `CorrelationGate.lean`, `diagnose_correlated_coefficients.py`.
- Lean proven: original even source coefficient equals `sourceJet`; normalized chart reciprocal scaling; finite head/Gamma reference factorization; normalized outer jet is a degree-12 polynomial in one shared `log(pi)` variable.
- Direct Lean command with `-DwarningAsError=true`: passed after expanding only the finite 0–12 coefficient identities.
- Exact-rational diagnostic passed: C3/48 finite coefficients fit the seven existing candidate balls after Gamma+tail allowance `2.48e-24`; minimum slack `6.30e-21` at `c4`.
- Tail source: exact original C3/48 Cauchy estimate, order-12 bound `1.5987e-24`; Gamma replacement is ledgered from the existing theorem.
- These calculations are not yet a Lean inclusion theorem or GREEN result. No positivity claim is made.
- No theta sign result, new axiom, or source change is used.
- Next exact action: formalize rational interval propagation for the normalized polynomial coefficients and prove all seven native coefficient enclosures.
- Open obligations: coefficient interval inclusion; rigorous Gamma+tail transport into candidate balls; final odd-block PosDef/pivot theorem; final axiom/dependency audit.
