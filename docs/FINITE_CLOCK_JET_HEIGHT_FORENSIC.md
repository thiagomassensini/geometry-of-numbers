> Recuperação canônica de 3 de outubro de 2026: fonte e status históricos preservados abaixo.
> Os caminhos antigos e frases sem commit/push descrevem a execução original.
> A versão atual vive em `GeometryOfNumbers/Analysis`; ver `RECOVERY_2026-10-02.md`.

# Finite clock jets and the historical height pipeline

## Forensic gate (before Lean reconstruction)

Worktree: `/home/thlinux/carry-finite-clock-jet-height`, branch
`codex/finite-clock-jet-height-2026-10-02`, base HEAD
`cb33c845a7ee0ca1c6bf195d34d7f3ac1628edfa`.
The dirty downstream C2/Green/Parseval sources are copied byte for byte;
their hashes are recorded in `FROZEN_INPUTS.json` in the evidence bundle.
No previously closed module is edited. No commit, merge or push is performed.

Exact historical sources:

| Role | Original path | SHA-256 |
|---|---|---|
| clock/port demo | `/home/thlinux/carry-lab/Arquivo/scripts/native_carry_selfadjoint_operator_demo.py` | `de10b88fc7939b5cb8e6c2fb8768dd7279ef301bf1c9f78b236825fbea24051d` |
| height builder containing all four requested functions | `/home/thlinux/carry-lab/FORMALIZANDO/native_carry_r2_height_operator_parallel_order_audit.py` | `c829bd77d4553d0c2699a224df4dafe7095471467570f4c065080e42b7509e40` |
| older integral-tail variant | `/home/thlinux/native_autoadjunto.py` | `aaa2f5860f2bbb10373017176c3d6dca0a674bdbe13f141cf23efbeede774396` |

These Python files are external artifacts, not tracked by the operator repo;
no Git commit is claimed for them. The Organizar copy of the demo has the
same hash. Exact source copies are preserved in
`/home/thlinux/finite-clock-jet-height-artifacts-2026-10-02/historical`.

The demo uses `n=1,...,state_dimension`, `log(n)`, amplitudes `n^(-1/2)`;
default cameras are 2,...,7 and native cutoff is 8. Its state dimension comes
from the camera readout and normalized colligation, not from the cutoff alone.
`native_readout_matrix` takes the maximum material support across those
cameras, giving state_dimension=59 for the defaults. `normalized_colligation`
builds residual/node endpoint rows, Green endpoint/bulk rows and whitens their
combined quadratic form before transporting the fixed camera readout.
It constructs a fixed normalized analysis V=(E,B), a Poisson map, and a full
camera readout; its generator is V diag(log n) V* plus zero on the gauge sector.
It does not construct phi, logarithmic moments, Jacobi, or heights.

The height script uses defaults CAMERA=2, CUTOFF=2, ORDER=50, DPS=500.
These can be overridden by its NATIVE_* environment variables. Distinguish:

- C: camera-center cutoff;
- M: material coordinate dimension; for the finite head M=p*C+max(radii);
- d: Jacobi/moment order (ORDER), unrelated to M;
- D=4*d: temporal Taylor truncation degree.

For camera=2 the period p is 4 and radii/seeds are (1,). Otherwise p=camera
and seeds/radii are 1,...,floor(camera/2). The finite weight map adds +1 at
each seed and, for k=1,...,C, adds -2*#radii at p*k and +1 at p*k +/- radius.
Coordinates are positive material integers; the Lean Fin M coordinate j
represents exactly n=j+1.

## Literal operations before extraction of phi

1. `native_state_series(n,D)` is the pair-valued Taylor series of
   n^(-1/2) exp(-i*t*log n).
2. `finite_chunk_series` scalarizes these coordinate series immediately by
   summing with the signed integer weights from `finite_weight_map`.
3. `exact_tail_scalar_taylor` adds a separately computed tail. Its production
   implementation is a finite Euler--Maclaurin calculation, despite the
   function name `exact_tail`: `em_terms=max(16,mp.mp.prec//3)`; that many
   head terms and Bernoulli corrections are used. It includes integral and
   half-endpoint terms, rising factorial polynomials, and exponentials of
   logarithms of endpoints. No rigorous remainder bound is returned.
4. For C+1=q, camera=2 combines tail germs at 4q-1, scaled (2,2q),
   scaled (4,q), with weights 1,-1,-2. Odd cameras combine first integer
   p*q-floor(p/2) and scaled (p,q), with weights 1,-p. Even cameras combine
   that first integer, scaled (p,q+1/2), scaled (p,q), with weights 1,1,-(p+1).
5. The scalar real-axis tail coefficients are multiplied by quarter(k)=i^k
   to return to temporal complex/pair coefficients. The optional reference
   instead uses a Mellin integral with x^(-1/2) log(x)^k, divided by k!,
   then multiplication by the reciprocal Gamma(1/2+i*t) germ.
6. The finite head and tail are added.
7. Formal series division by the camera factor B(t):
   camera=2: 1-2^(-1/2)e^(-it log2)-2*4^(-1/2)e^(-it log4);
   odd camera: 1-sqrt(p)e^(-it log p);
   even camera: 1+a^(-1/2)e^(-it log a)-(camera+2)p^(-1/2)e^(-it log p),
   a=max(radii). This division requires B(0) nonzero.
8. Multiplication by the separate completion germ
   A(t)=1/2*(-1/4-t^2)*pi^(-1/4)e^(-it log(pi)/2)*Gamma(1/4+i*t/2).
   The Gamma germ is computed by exponentiating the polygamma series of
   log Gamma; it is not obtained from the finite material clock.
9. Extract `phi[r]=characteristic[2*r][0]`: take the REAL quadrature of the
   EVEN temporal coefficients. No proof of exact evenness is performed by
   this numerical extraction.

Consequently, write F(t)=A(t)*(head(t)+tail(t))/B(t) for the full temporal
response germ. The moments actually use Phi(u)=sum phi[r]*u^r, u=t^2,
with phi[r]=Re([t^(2r)]F). In analytic terms when the germs are identified,
phi[r]=Re(F^(2r)(0))/(2r)!, NOT F^(r)(0) and NOT its raw derivative.

Completion mixes lower clock jets by convolution. Even with a fixed scalar
head readout R, phi[r] involves all normalized head jets through order 2r,
plus tail/factor/completion coefficients. It is not in general R of the
single order-r clock jet. The formal bridge must keep these other germs
as explicit inputs, rather than call them derived from L_M.

## Provenance gate

The historical head uses n^(-1/2) amplitudes and signed camera brackets.
The frozen modern C2 source uses provenance-correct branch/depth amplitudes
and material phases. The historical height script has no JW_tV construction,
no branch/camera incidence carrier, no TFVD/Green synthesis and no canonical
Parseval analysis before its early scalar sum. Its later completion adds
analytic tail and Gamma/pi data independently.

This is a provenance gap, not a claim that the amplitude n^(-1/2) is
algebraically incompatible with dyadic factorization: for n=2^k*m it equals
2^(-k/2)*m^(-1/2). Such an amplitude coincidence does not supply the missing
incidence/synthesis/completion bridge or identify the independently added tail.

Thus the actual finite-head clock crosswalk is valid, but does not certify
that its completed phi is a readout of the provenance-correct C2/Green source.
No such additional bridge is assumed. The full closed response is not a
finite sum of the M material exponentials: the tail and completion are
additional inputs. In particular, finite Taylor degree and finite Jacobi
order do not turn this response into a purely finite-state clock orbit.

## Exact downstream conventions

`logarithmic_moments` uses h_r=(-(r+1)phi_(r+1)-sum_(j<r)h_j phi_(r-j))/phi_0,
the coefficient identity H(u)Phi(u)=-Phi'(u), with phi_0 nonzero.
h_r uses only phi_0,...,phi_(r+1), so requires temporal coefficients through
2r+2, not r+1. For order d, moments through 2d-1 require phi through 2d,
and temporal jets through 4d (matching the literal degree=4*d).

The Hankel objects are G_ij=h_(i+j), K_ij=h_(i+j+1).
The production recurrence rescales h_r to a_r=c^r h_r, c=1/h_0, and uses
the Chebyshev/modified-moment recurrence on a. beta[0]=a_0 is the mass;
beta[k], k>=1, is the SQUARED off-diagonal. The matrix has diagonal alpha[k]
and off-diagonal sqrt(beta[k]); beta[k]<=0 raises an exception.
The old integral-tail script instead uses Cholesky congruence without this
rescaling. These are separate exact implementation conventions.

The current generic Lean counterparts are hankelGram, shiftedHankel,
finiteJacobiTransport/finiteJacobiSection, canonicalHankelWhitening,
canonicalFiniteJacobiSection, finiteHeightOperator. They certify the moment
matrix/congruence/positive height steps under their stated hypotheses.
The Python Chebyshev loop is not silently identified with canonical LDL
whitening; a theorem identifying that loop with the same canonical factor
would be an additional implementation crosswalk.

The production height transform is t_j=sqrt(c/Y_j), where Y_j are eigenvalues
of the RESCALED Jacobi matrix and c=1/h_0. All Y_j must be strictly positive;
zero and negative Y_j are rejected. For a real positive height interpretation
c must also be positive (h_0>0); the helper checks Y_j explicitly but does
not independently check c. `eigsy` supplies the spectral coordinates; output
heights are sorted separately. Functional calculus uses the UNSORTED heights
paired with the original eigenvectors, H_height=Q diag(t_j) Q^T.
This selected script is unsigned. No target spectrum or zeros are inputs to
this reconstruction.

## Operator distinctions

- Finite clock L_M: eigenvalues log 1,...,log M.
- Finite Jacobi J_d: eigenvalues Y_j (for the selected scaled moment convention).
- Finite height H_height,d: eigenvalues sqrt(c/Y_j), on the positive domain.

No equality or unitary conjugation between clock and height is asserted.

## Status

Forensic outcome: HISTORICAL_SCALARIZATION_MISMATCH. The finite clock/head
jet identity can be certified independently. The completed historical phi
requires extra tail and dressing germs and an unproved provenance bridge
to the modern source. A full unconditional clock-to-height PASS would hide
these seams.

## Certified finite results

`FiniteMaterialClockJets.lean` reuses the existing finite CPFormal generator
and unitary orbit. Its material basis index is explicitly j+1. It proves:

- `finiteMaterialClock_basis`, `finiteMaterialOrbit_basis`;
- `finiteMaterialClockJet_eq_generatorPow` and `finiteMaterialClockJet_basis`,
  using actual real-parameter `iteratedDeriv`, for every finite Hilbert vector;
- `historicalQuarter_eq_I_pow` and `historicalRotationCoefficient_exact`;
- `nativeStateSeries_eq_normalizedClockJet` and `nativeStateSeries_quadratures`;
- `historicalCameraWeights_default`: the literal production head is
  [1,0,1,-2,1,0,1,-2,1] on material integers 1,...,9;
- `finiteClockJets_to_head` and `finiteHeadReadout_iteratedDerivative`;
- `finiteMaterialOrbit_coordinate_hasSum` and `finiteHeadReadout_hasSum`,
  globally recovering the finite orbit/head from its Taylor tower.

`FiniteClockHeightLedger.lean` defines the formal closed-response pipeline
A*(head+tail)*B^(-1), keeping all three external germs explicit. It proves:

- the camera-quotient identity under B(0) nonzero;
- `finiteClockJets_to_phi_with_external_germs`, the exact nested convolution
  for Re([t^(2r)]F);
- `finiteClockJets_determine_phiPrefix`: fixed external germs and normalized
  head readouts through order 4d determine phi through 2d;
- the literal recursive moments, agreement with the existing moment relation
  by its uniqueness theorem, the formal identity H(u)Phi(u)=-Phi'(u), and
  `finiteLogMoment_formal_quotient`, H(u)=-Phi'(u)/Phi(u), when phi_0 is nonzero;
- triangular moment dependence and the rescaled Hankel pair;
- `finiteClockJets_determine_JacobiSection`, for the EXISTING canonical LDL
  section, with fixed external germs and the required Gram positivity;
- the exact Q diag(sqrt(scale/Y)) Q* formula and characteristic polynomial,
  positivity of heights under scale>0 and J>0, and equality with the existing
  `finiteHeightOperator` at scale=1.

`externalTail_changes_phi_zero` is a formal guard against dropping external
inputs: keeping the complete head/clock tower unchanged, adding a constant
one to the independently supplied tail changes phi_0 by one (B=A=1).

`FiniteHistoricalChebyshev.lean` separately transcribes the selected script's
finite modified-moment loop, including zeroed array ranges, beta[0] as mass,
and square roots of beta[k] only for off-diagonals. It proves symmetry,
dependence only on moments below 2d, and:

- `finiteClockJets_determine_historicalChebyshev`;
- `historicalChebyshevHeight_charpoly`;
- `finiteClockJets_determine_historicalHeight`.

These last dependencies hold relative to identical external germs and,
for heights, strict Jacobi positivity. Successful Python divisions additionally
require the explicitly recorded nonzero denominator gates. The totalized Lean
definitions do not prove that these gates hold for the historical concrete
coefficients. The exact-arithmetic transcription is not a proof of arbitrary-
precision rounding correctness.

The new Chebyshev matrix and existing canonical LDL matrix are kept distinct.
Their equality for the concrete historical coefficient family is not a Lean
theorem here. A regression at camera=2, cutoff=2, d=3, D=12, 70 decimal digits
compares them after the same rescaling and finds discrepancy below 1e-70;
rotation coefficients agree below 1e-70. This is numerical evidence only.

## Where t went, and what is not certified

For the finite material orbit and scalar head, the complete Taylor tower
recovers the temporal scan for every real t (proved by `HasSum`). For a chosen
finite output order d, the code needs only jets through 4d and explicitly
supplied external germs through that same degree.

For the full historical completed response, this round does not prove its
analytic germs equal those of a provenance-correct modern Green source, nor
that the production Euler--Maclaurin tail has no error. It also does not infer
full-response recovery from the extracted real even coefficients without
symmetry/analyticity certificates. These are distinct from the finite-head
Taylor theorem. No infinite-domain gate, analytic-vector argument, Hankel
limit, or spectral convergence is used.

## Validation and preservation

The rejecting audit covers all 74 public declarations in the three modules,
including their private dependencies transitively, and allows only
`propext`, `Classical.choice`, `Quot.sound`. Final build and direct-audit logs,
exact source copies, historical hashes, the regression, and preservation
checks are saved in `/home/thlinux/finite-clock-jet-height-artifacts-2026-10-02`.
The four frozen C2/Green/Parseval modules and all copied downstream files are
checked byte for byte against `FROZEN_INPUTS.json`; the tracked upstream
operator modules are also checked against the base commit.

## Final classification

**HISTORICAL_SCALARIZATION_MISMATCH — the historical height script scalarizes
or modifies the state before the stage represented by the provenance-correct
modern source, so its phi_r cannot yet be claimed as readouts of the
reconstructed source without an additional bridge.**

The certified chain is the finite material clock -> normalized head jet
readouts -> completed coefficients RELATIVE TO external germs -> recursive
moments -> finite Jacobi constructors -> positive finite height calculus.
It does not certify an unconditional L_M-only origin of the complete
historical phi family. No clock/height equality or unitary conjugation is
introduced.
