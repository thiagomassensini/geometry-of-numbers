# Checkpoint — correlated C3 coefficient gate

- Phase: correlation audit; branch `agent/c3-cofactor-correlation-gate-20261112` starts at merged PR #322, base `de8f044d78260fd4ba9f728c3bb313adfa0255df`.
- State: clean branch; no source files modified yet.
- Reused proofs: PR #322 cofactor identity, order-11 transport, C3/48 head boxes, Gamma crosswalk, literal head/tail decomposition, original tail estimate.
- New finding: preserving the shared `log(pi)` variable through a Horner polynomial removes the previous `~1e-16` interval blow-up in the normalized order-12 outer jet.
- Exact-rational diagnostic: the existing seven candidate coefficient balls contain the C3/48 finite reference jets after a conservative `4.16e-23` native-Gamma/tail allowance; smallest slack is about `6.26e-21` at `c4`.
- This is not yet a Lean theorem or a GREEN result. The diagnostic still needs a Lean-checked source crosswalk and coefficient enclosure.
- Tail improvement: the proved C3/48 Cauchy estimate gives order-12 error `<2e-24`; for all orders through 12 the same upper bound applies.
- Next exact action: implement a Lean module that factors the original finite source into normalized head jets and a shared-variable outer polynomial, then prove the seven native coefficient inclusions.
- Open obligations: chart-reciprocal normalization identity; interval Horner enclosure for the shared `log(pi)`; scalar factor bounds; transfer of Gamma and tail errors into candidate boxes; final odd-block PosDef/pivot theorem.
- No theta positivity, new axioms, or source modifications are used.
