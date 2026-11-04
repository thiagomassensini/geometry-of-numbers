# Broad validator preflight result

Date checked: 2026-11-04.

`validate.py` computes the Carry checkout as
`/home/thlinux/worktrees/carry-self-adjoint-operator`, a path that does not
exist in this environment. The existing checkout is
`/home/thlinux/carry-self-adjoint-operator`.

After a temporary symlink pointed the expected path at the existing checkout,
the validator stopped at its line 45 assertion:

```text
assert not read('git','diff','HEAD','--',cwd=operator)
```

The checkout has pre-existing modified tracked files
`CarrySelfAdjointOperator/ThetaSixteenthFloorCertificateData/Aggregator.lean`
and `scratch_local/BoundaryEnergy.lean`, as well as untracked work including
`CarrySelfAdjointOperator/C2OddTfvdTransport.lean`,
`CarrySelfAdjointOperator/C2OddTfvdTransportAudit.lean`, and generated files
under `scratch_local/`. The validator aborted before its checks; none of these
files was changed or removed. The temporary symlink was removed immediately
after observing the preflight failure.

The focused `SecondSchur` build and transitive `Audit` build both pass; their
logs are `second-schur-build.log` and `second-schur-audit.log`.
