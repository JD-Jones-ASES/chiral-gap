# chiral-gap

Exact robust spectral gaps for **finite open chiral chains**, with arbitrary
inhomogeneous strong-bond bounds and complex matrix disorder. The Lean proof
finds the worst scalar gap among the ordered one-switch configurations,
classifies every scalar minimizer when weak lower bounds are positive, and
proves the sharp channel bound and its complete equality criterion.

The full mathematical account is in [Proof.md](Proof.md).
[Note.md](Note.md) records the source attribution, interval-matrix comparison
and limits of the prior-art assessment.

## Scalar value and minimizers

For $N\ge2$ sites, positive strong bounds $\beta_i$, boundary parameter
$s\ge0$, and ratios $q_i\in[\ell_i,\rho_i]$ with $0\le\ell_i\le\rho_i$, set

```math
E_q(x)=s^2x_1^2+\sum_{i=2}^{N}(x_{i-1}-q_i x_i)^2+x_N^2,
\qquad M_\beta(x)=\sum_{i=1}^{N}\frac{x_i^2}{\beta_i^2}.
```

The literal rectangular residual matrix $Q(q)D_\beta$ has Gram matrix
$K(q)=D_\beta Q(q)^TQ(q)D_\beta$. Its least eigenvalue is the minimum of
$E_q/M_\beta$. The squared robust gap is

```math
L=\min_{\ell\le q\le\rho}\lambda_{\min}K(q)
 =\min_{1\le k\le N}\lambda_{\min}K(q^{(k)})>0,
\qquad
q_i^{(k)}=\begin{cases}\ell_i&i\le k,\\\rho_i&i>k.\end{cases}
```

The proof establishes attainment and positivity from these actual matrices.
Zero bounds and fixed intervals are included. If every $\ell_i=0$, only
two scalar certificates are needed: the fully saturated chain and its
saturated zero-left-boundary suffix on sites $2,\ldots,N$.

When every $\ell_i>0$, all minimizing configurations form either one
one-switch vertex or one full transition interval: lower endpoints before
one free coordinate, upper endpoints after it. Fixed intervals may collapse
that interval to a point. An exact greedy Schur-pivot rule identifies the
entire set. A tie can occur at most once. The formal indexing uses $n$ edges
and $n+1$ sites, and also includes the one-site case.

## Matrix channels and the physical gap

Let the channel space have any positive finite complex dimension $d$.
For invertible strong bonds $B_i$ and weak bonds $A_i$, put
$R_i=A_iB_i^{-1}$, in that order. Assume

```math
\sigma_{\min}(B_i)\ge\beta_i,\qquad
\sigma_{\min}(R_1)\ge s,\qquad
\ell_i\le\sigma_{\min}(R_i)\le\|R_i\|\le\rho_i\quad(i\ge2).
```

The actual tall hopping operator is

```math
\mathcal A y=(A_1y_1,\ B_1y_1+A_2y_2,\ldots,
 B_{N-1}y_{N-1}+A_Ny_N,\ B_Ny_N).
```

Then $\|\mathcal A y\|^2\ge L\|y\|^2$. The formal hypotheses use the
equivalent directional norm inequalities, avoiding conventions about the
ordering of singular values. No commutation or common eigenbasis is assumed.
Scalar identity bonds attain the bound in every positive channel dimension
and satisfy every stated operator constraint.

The chiral block operator

```math
H=\begin{pmatrix}0&\mathcal A\\\mathcal A^*&0\end{pmatrix}
```

has a kernel of dimension exactly $d$. Its nonzero spectrum is precisely
the two signs of the $Nd$ singular values of $\mathcal A$, with an explicit
isomorphism between the corresponding eigenspaces. Every nonzero energy
has magnitude at least $\sqrt L$. The attaining construction has both
$+\sqrt L$ and $-\sqrt L$ as actual eigenvalues.

With strictly positive weak lower bounds, equality holds exactly when a
scalar minimizing configuration supports aligned unit channel vectors
$u_i$ satisfying

```math
u_i\in\ker(B_iB_i^*-\beta_i^2I),\qquad
u_1\in\ker(R_1^*R_1-s^2I),\qquad
R_i u_i=-q_i u_{i-1}\quad(i\ge2).
```

The proof derives this from equality in every norm comparison. The Lean
criterion is first stated using the equivalent norm-attainment conditions;
`EqualitySubspaces.lean` proves the exact translation to these kernels.

## Formal proof and verification

[`ChiralGapChallenge.lean`](ChiralGapChallenge.lean) is the independent,
Mathlib-only statement file. Every definition in it has its complete value.
[`ChiralGapSolution.lean`](ChiralGapSolution.lean) imports the proofs.
[`comparator.json`](comparator.json) lists the precise declarations checked
against the independent statements.

The proof has four main parts:

- `Variational`, `ScalarGram`, `Scalar`, `Value` and `TwoCertificates` connect
  the literal matrix to compact optimization and prove the value reductions.
- `GreedyChain`, `GreedyExistence` and `Equality` construct the optimum pivots
  and classify all minimizing configurations.
- `Channels`, `ChannelEquality`, `EqualityChannels` and `EqualitySubspaces`
  prove the arbitrary-channel comparison and equality directions.
- `Spectral`, `SpectralAttainment`, `ChannelSpectral` and `Principals` connect
  the hopping map, singular values, actual chiral spectrum and sharpness.

The cut-allowed boundary-threshold classification, ordered boundary
transitions and determinant stability estimate in [Proof.md](Proof.md) are
supplementary written theorems, outside the Comparator contract. The positive-lower-bound hypothesis is essential for
the point-or-edge classification. Cyclic, infinite-volume and interacting
many-body models are outside the result.

With Elan installed, reproduce the pinned development using:

```sh
lake exe cache get
lake build
lake comparator --config comparator.json
```

Comparator requires Linux with bubblewrap. The manual GitHub Actions workflow
builds the exact checked-out commit, audits every compared theorem's
transitive axioms, compares statements and definitions, and replays the
exported proofs through Lean, NanoDa and con-ron. A separate fresh-runner
build checks reproducibility. Project proof outputs are never cached.
Only `propext`, `Quot.sound` and `Classical.choice` are permitted. Intentional
`sorry` placeholders occur only in the independent Challenge.

JD Jones is the responsible human maintainer. [Disclosure.md](Disclosure.md)
and [formalization.yaml](formalization.yaml) record the original GPT 6 Pro
contribution, subsequent GPT-6 Astra work and internal agent review. Worldwide
priority and independent human specialist review remain unestablished.
