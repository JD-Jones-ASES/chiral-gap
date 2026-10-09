# Exact robust gaps for finite open chiral chains

This account proves the one-switch value theorem, its two-certificate
special case, sharp arbitrary-channel transfer and the complete scalar and
matrix equality classification with strictly positive weak-bond lower bounds.
It also proves ordered boundary transitions and quantitative stability.
The claims concern finite open chains with deterministic bounds.

The original two-certificate, one-switch and channel-transfer argument came
from the GPT 6 Pro draft supplied by JD Jones. The positive-interval optimizer,
stability and equality-channel extensions were developed with GPT-6 Astra.
[Note.md](Note.md) records provenance and the prior-art comparison;
[README.md](README.md) records the scope of machine verification.

## Model and exact value

Fix n>=2, beta_i>0, s>=0 and 0<=ell_i<=rho_i for 2<=i<=n. For real x set

```math
E_q(x)=s^2x_1^2+\sum_{i=2}^n(x_{i-1}-q_i x_i)^2+x_n^2,
\qquad M_\beta(x)=\sum_{i=1}^n x_i^2/\beta_i^2.
```

Let Q(q)x=(s x_1,x_1-q_2x_2,...,x_{n-1}-q_nx_n,x_n),
D=diag(beta_i), and K(q)=D Q(q)^T Q(q)D. Thus K has diagonal
beta_1^2(1+s^2), beta_i^2(1+q_i^2), and adjacent off-diagonal
-beta_{i-1} beta_i q_i. The last n rows of Q(q)D are invertible upper
bidiagonal, so K(q) is positive definite. Define the attained minimum

```math
L=\min_{q_i\in[\ell_i,\rho_i]}\lambda_{\min}K(q)>0.
```

**Theorem 1 (one-switch value).** Define q^(k)
by q_i=ell_i for i<=k and q_i=rho_i for i>k, for k=1,...,n. Then

```math
L=\min_{1\le k\le n}\lambda_{\min}K(q^{(k)}).
```

This includes zero and fixed intervals. Here and below L is a **squared**
singular-value gap. The physical excitation gap is sqrt(L).

**Proof.** Let L0 be the right-hand minimum and fix 0<lambda<L0. After
congruence by D^-1, the Schur pivots of K(q)-lambda I satisfy

```math
a_1=1+s^2-\lambda/\beta_1^2,\qquad
a_j=1-\lambda/\beta_j^2+q_j^2(1-1/a_{j-1}).
```

While a>0, the update is nondecreasing in a. At a given preceding pivot
its least value uses ell_j if a>=1 and rho_j if a<1. Construct this greedy
sequence. Each chosen prefix extends to a one-switch candidate, whose
positive definiteness proves positivity of the next pivot. Once a pivot
is <=1, the next is strictly below 1 because lambda>0. Thus the greedy
choices never return from upper to lower endpoints. Induction compares
every other admissible pivot sequence to the positive greedy sequence,
using first monotonicity in a and then minimization in q_j. Sylvester's
criterion gives K(q)>lambda I for every q. Let lambda increase to L0.
The reverse inequality follows from the admissibility of the candidates.

## Two certificates when cuts are allowed

Suppose ell_i=0. Let F=K(rho_2,...,rho_n). Let S be the matrix on
coordinates 2,...,n of

```math
\sum_{i=3}^n(x_{i-1}-\rho_i x_i)^2+x_n^2
```

with mass sum_{i=2}^n x_i^2/beta_i^2; equivalently conjugate its Gram
matrix by diag(beta_2,...,beta_n). For n=2 this is [beta_2^2]. Write
f=lambda_min(F), delta=lambda_min(S).

**Theorem 2 (two certificates).**

```math
L=\min\{f,\delta\}.
```

Here is a direct proof which includes zero envelopes and semidefinite
endpoints. For N>=1 and envelopes rho_i>=0, on coordinates 0,...,N define

```math
\mathcal Q_{d,q}(x)=\sum_{i=0}^N d_ix_i^2+
\sum_{i=0}^{N-1}(x_i-q_ix_{i+1})^2,
\qquad d_i\le0\ (0<i<N).
```

This form is nonnegative for every 0<=q_i<=rho_i iff the saturated form
and the saturated suffix on x_0=0 with q_0=0 are nonnegative.

For a chosen edge k, scale its strict suffix by t (operator L_t) and
project onto that suffix (operator P). A termwise identity is

```math
\mathcal Q_{q_k=rt}(x)=\mathcal Q_{q_k=r}(L_tx)
 +(1-t^2)\mathcal Q_{q_k=0}(Px).
```

It proves positivity throughout the box from positivity at its vertices.
At a vertex the cut edges split the form into blocks. The first block is
a restriction of the fully saturated form. To control a later block,
first consider its saturated suffix starting at j>1. Extend a test vector
backwards by x_i=rho_i x_{i+1}, down to i=1, and set x_0=0 with the first
edge cut. Added residuals vanish and added diagonal terms are nonpositive.
Thus positivity of the longest suffix forces positivity of this shorter
suffix. Restriction on the right then controls the original block. Sum
over blocks and use the identity. Necessity follows by specialization.

Apply this equivalence to E_q-lambda M_beta at
lambda=min(f,delta). Its interior diagonal terms are -lambda/beta_i^2.
This proves K(q)>=lambda I. Saturation attains f when f<=delta.
When delta<=f, choose q_2=0 and all later ratios saturated. The resulting
matrix is diag(beta_1^2(1+s^2),S); its first entry is >=f>=delta by the
coordinate Rayleigh test on F. It attains delta.

## Boundary threshold with positive envelopes

Suppose all rho_i>0. Then

```math
\operatorname{sign}(f-\delta)=
\operatorname{sign}(\beta_1^2s^2-\delta).
```

Indeed the trailing block of F is S+beta_2^2 rho_2^2 e_1e_1^T.
Its smallest eigenvalue is >delta: a minimizing eigenvector of the
irreducible Jacobi matrix S is nonzero in its first coordinate. Interlacing
then leaves at most one eigenvalue of F at or below delta. Expansion gives

```math
\det(F-\delta I)=\beta_2^2\rho_2^2
 (\beta_1^2s^2-\delta)C,
```

where C is the determinant of the strict trailing principal block of
S-delta I, positive by strict interlacing (C=1 for n=2).

The minimizing scalar magnitudes are uniquely all saturated below the
threshold, uniquely q_2=0 with later ratios saturated above it, and exactly
that full q_2 interval with later ratios saturated at the threshold.
For completeness, the vertex argument is strict: proper saturated prefixes
have lowest eigenvalue >f by interlacing; shorter zero-boundary suffixes
have lowest eigenvalue >delta. For the latter, the inverse of the upper
bidiagonal suffix has entries beta_i^-1 product_{r=i+1}^j rho_r (i<=j).
Removing its first rows/columns strictly decreases its norm, by testing
the positive top singular vector of the shorter inverse in the longer one.
Right truncation is again strict interlacing. Hence the only minimizing
vertices are the stated one or two vertices. The full determinant of
K(q)-L I is multiaffine in q_i^2 by its continuant recurrence; it is a
convex combination of nonnegative vertex determinants. Its zero set is
therefore exactly the stated vertex or edge. Positivity already proved
turns determinant zeros into lowest-eigenvalue equality.

## Sharp arbitrary-channel transfer

Let B_i and A_i be complex d by d matrices, with B_i invertible, and set
R_i=A_i B_i^-1 in that order. Define the tall hopping operator

```math
\mathcal A y=(A_1y_1,B_1y_1+A_2y_2,...,
B_{n-1}y_{n-1}+A_ny_n,B_ny_n).
```

Assume sigma_min(B_i)>=beta_i, sigma_min(R_1)>=s, and
ell_i<=sigma_min(R_i)<=||R_i||<=rho_i for i>=2. Then

```math
\sigma_{\min}(\mathcal A)^2\ge L,
```

and this is sharp for every channel dimension d. No simultaneous
diagonalization, commutation, probability law, or condition rho_i<1 is used.

Put z_i=B_i y_i, x_i=||z_i||. If x_i>0 choose the actual ratio
q_i=||R_i z_i||/x_i in [ell_i,rho_i]; if x_i=0 choose any admissible ratio.
The reverse triangle inequality gives
||z_{i-1}+R_i z_i||^2 >= (x_{i-1}-q_i x_i)^2. Thus

```math
\|\mathcal Ay\|^2\ge E_q(x)\ge L M_\beta(x)
\ge L\sum_i\|y_i\|^2.
```

This form of the comparison retains the actual directional ratio. The
draft instead minimizes over the interval, which gives the same bound.
Sharpness follows by B_i=beta_i I, R_1=s I, R_i=-q_i I at a scalar minimizer.
The equality theorem below identifies all equality realizations when ell_i>0.

The chiral Hamiltonian H=[[0,A],[A*,0]] has exactly d zero eigenvalues and
nonzero eigenvalues plus/minus the nd singular values of A: delete the
first block row to obtain an invertible upper block-bidiagonal operator.
Therefore the minimum nonzero |energy| is >=sqrt(L), with sharpness.
This is a finite single-particle gap theorem. It is not a many-body,
bulk-edge, mobility-gap, or topological-phase theorem.


## Positive weak-bond lower bounds

For the following four results assume additionally that every ell_i>0.

## Theorem 3: the complete scalar minimizer set is one face

Define a greedy pivot sequence at the exact value `L` by

```math
 a_1=1+s^2-L/\beta_1^2,
 \qquad
 a_j=1-L/\beta_j^2+v_j^2(1-1/a_{j-1}),\quad 2\le j\le n,
```

where `v_j=ell_j` if `a_(j-1) >= 1`, and `v_j=rho_j` otherwise.
Then `a_j>0` for `j<n`, `a_n=0`, and the entire minimizer set is

```math
 \mathcal M=\left\{q:
 \begin{array}{ll}
 q_j=\ell_j&\text{if }a_{j-1}>1,\\
 q_j=\rho_j&\text{if }a_{j-1}<1,\\
 q_j\in[\ell_j,\rho_j]&\text{if }a_{j-1}=1
 \end{array}\quad(2\le j\le n)\right\}.
```

There is at most one index with `a_(j-1)=1`. Consequently `M` is either a
single vertex or one complete edge, with all lower endpoints before the free
coordinate and all upper endpoints after it. Degenerate intervals are simply
fixed coordinates. If all intervals are nondegenerate, exactly one candidate
`q^(k)` minimizes, or exactly two adjacent candidates minimize and their whole
connecting edge is the minimizer set.

### Proof

**Proper prefixes remain positive definite at the optimum.** For every allowed
`q`, `K(q)-LI` is positive semidefinite. Every proper leading principal block
is positive definite. Indeed, if a leading block had a nonzero kernel vector,
extend it by zero to all coordinates. Its quadratic form under `K(q)-LI`
vanishes, so positive semidefiniteness makes the extended vector a full kernel
vector. The first omitted row then forces the last retained coordinate to
vanish because the crossing off-diagonal entry is nonzero. Recurrence along
the nonzero off-diagonal entries forces every retained coordinate to vanish,
a contradiction. Positive semidefiniteness and this argument also apply after
congruence by `D_beta^-1`.

Therefore every admissible parameter vector has positive normalized Schur
pivots through index `n-1`, and a nonnegative last pivot. All greedy prefixes
are admissible prefixes and can be extended within the box, so the displayed
recursion is defined without division by zero.

**Greedy pivots are pointwise minimal.** Write

```math
 F_j(a,q)=1-L/\beta_j^2+q^2(1-1/a).
```

For `a>0` and `q>0`, this is strictly increasing in `a`, since
`partial F_j/partial a=q^2/a^2>0`. At fixed `a`, its minimum on the allowed
interval is at `ell_j` if `a>1`, at `rho_j` if `a<1`, and at every point if
`a=1`. Induction therefore gives `b_j(q)>=a_j` for the pivots of every `q`.
A minimizing matrix is singular after subtracting `LI`, so its last pivot is
zero. The greedy last pivot is nonnegative and no greater, hence `a_n=0`.

**Equality propagates backwards.** Suppose `q` minimizes. At each step,

```math
 b_j=F_j(b_{j-1},q_j)
       \ge F_j(a_{j-1},q_j)\ge a_j.
```

Starting from `b_n=a_n=0`, equality in the first inequality forces
`b_(n-1)=a_(n-1)` because `q_n>0`; equality in the second forces the stated
endpoint rule. Repeat backwards. Conversely the stated rules give equality
of every pivot, hence a zero last pivot and a minimizing matrix.

Finally, if `a_(j-1)<=1`, then

```math
 a_j=1-L/\beta_j^2+v_j^2(1-1/a_{j-1})<1.
```

Once the pivots are below one they remain below one. There is at most one
tie, completing the classification. This proof also independently recovers
the one-switch value theorem when all lower bounds are positive.

## Corollary 4: the switches occur in path order as the boundary grows

Assume here that every interval is nondegenerate. For `2<=j<=n`, let `S_j`
be the saturated zero-left-boundary suffix on coordinates `j,...,n`, and write
`delta_j=lambda_min(S_j)`. Explicitly its energy is

```math
 \sum_{i=j+1}^n(x_{i-1}-\rho_i x_i)^2+x_n^2
```

with the same weighted mass on that suffix. Then
`0<delta_2<...<delta_n=beta_n^2`. If the minimizing vertex has lower
endpoints through `k` and upper endpoints after `k`, then

```math
 \begin{cases}
 L<\delta_2,&k=1\text{ and the vertex is unique},\\
 \delta_k<L<\delta_{k+1},&1<k<n\text{ and the vertex is unique},\\
 L>\delta_n,&k=n\text{ and the vertex is unique}.
 \end{cases}
```

The free-edge case at coordinate `j` occurs exactly when `L=delta_j`.
In particular the switch index is determined by the position of `L` among
these strictly ordered suffix eigenvalues.

### Proof

Strict suffix ordering follows by backward extension: extend a positive
ground vector of suffix `j+1` to coordinate `j` by
`x_j=rho_(j+1) x_(j+1)`. This adds zero energy and strictly positive mass, so
its Rayleigh quotient strictly decreases. The positive ground vectors exist
because the Jacobi matrices have strictly negative adjacent entries.

At a minimizer take the normalized-coordinate ground vector `x>0` and put
`r_(j-1)=x_(j-1)-q_j x_j`. Whenever all links after coordinate `j` are
saturated, multiply the tail eigen-equations by a positive ground vector
`w` of `S_j`. Symmetry gives the exact identity

```math
 (\delta_j-L)\sum_{i=j}^n w_i x_i/\beta_i^2
       =q_j r_{j-1}w_j.
```

The left side has the sign of `delta_j-L`. The prefix elimination equation
is `a_(j-1) x_(j-1)=q_j x_j`, hence
`r_(j-1)=(1-a_(j-1))x_(j-1)`. Apply this at the last lower link and first
upper link from Theorem 3. It gives the strict inequalities, or equality
exactly at the free link. The strict ordering of the `delta_j` and the complete
classification exhaust all cases.

For completeness, with all bounds fixed and `t=s^2`, each candidate's lowest
eigenvalue is continuous and strictly increasing in `t`. Strictness follows
from its positive first ground-vector coordinate and the variational principle:
testing the ground vector at a larger `t` at a smaller `t` strictly decreases
its Rayleigh quotient. The minimum of finitely many strictly increasing
functions is strictly increasing. Thus `L(t)` is continuous and strictly
increasing. At `t=0` its minimizing vertex is fully saturated because
`a_1=1-L/beta_1^2<1`. Any suffix threshold reached at a finite boundary value
is reached once, in increasing path order. Thresholds above the limiting
robust value need not be reached.

## Theorem 5: an explicit quantitative stability bound

Ignore degenerate intervals and put

```math
 t_j=\frac{q_j^2-\ell_j^2}{\rho_j^2-\ell_j^2}\in[0,1].
```

Let `J` be the nondegenerate coordinates fixed by the minimizing face `M`.
For `j in J`, define `eta_j=t_j` when that face fixes `q_j=ell_j`, and
`eta_j=1-t_j` when it fixes `q_j=rho_j`. Suppose `m=|J|>0`. Over all box
vertices outside `M`, define

```math
 D_* =\min_{v\notin\mathcal M}\det(K(v)-LI)>0,
 \qquad
 T=\beta_1^2(1+s^2)+\sum_{i=2}^n\beta_i^2(1+\rho_i^2).
```

Then every allowed `q` satisfies

```math
 \lambda_{\min}K(q)-L
 \ge \frac{D_*}{T^{n-1}}
       \left[1-\prod_{j\in J}(1-\eta_j)\right]
 \ge \frac{D_*}{mT^{n-1}}\sum_{j\in J}\eta_j.
```

This coefficient is explicit but is not asserted to be sharp. Computing
`D_*` by its definition may require all vertices; the `n`-candidate value
theorem is not a claim of an `n`-candidate stability-constant algorithm.
If `J` is empty, every allowed vector minimizes and the nonnegative bound
`lambda_min K(q)-L>=0` is the whole assertion.

### Proof

The leading determinant recurrence is

```math
 p_0=1,\quad p_1=\beta_1^2(1+s^2)-L,
```
```math
 p_j=(\beta_j^2(1+q_j^2)-L)p_{j-1}
           -\beta_{j-1}^2\beta_j^2q_j^2p_{j-2}.
```

It shows inductively that `det(K(q)-LI)` is multiaffine in the squared
couplings. Its exact multilinear interpolation on the box is a convex
combination of vertex determinants, using independent Bernoulli weights
`t_j`. All determinants are nonnegative. Exactly the vertices of `M` have
zero determinant, by positive semidefiniteness and Theorem 3. The total weight
outside that face is `1-product_(j in J)(1-eta_j)`, proving the determinant
lower bound.

Every eigenvalue of `K(q)-LI` is nonnegative and at most
`lambda_max(K(q))<=trace(K(q))<=T`. Factoring the determinant into eigenvalues
therefore gives
`det(K(q)-LI)<=(lambda_min(K(q))-L)T^(n-1)`.
Finally `1-product(1-eta_j)>=max eta_j>=sum eta_j/m`.

## Theorem 6: complete equality criterion for matrix channels

Let `B_i` be invertible complex `d` by `d` matrices, set `R_i=A_i B_i^-1`,
and let the tall operator be

```math
 \mathcal A y=(A_1y_1,
 B_1y_1+A_2y_2,\ldots,B_{n-1}y_{n-1}+A_ny_n,B_ny_n).
```

Assume

```math
 \sigma_{\min}(B_i)\ge\beta_i,\qquad
 \sigma_{\min}(R_1)\ge s,\qquad
 \ell_i\le\sigma_{\min}(R_i)\le\|R_i\|\le\rho_i\quad(i\ge2).
```

Define subspaces in the normalized site coordinates by

```math
 P_i=\ker(B_iB_i^*-\beta_i^2I),\qquad
 N_1=\ker(R_1^*R_1-s^2I).
```

Then `sigma_min(Acal)^2 >= L`, and equality holds if and only if there are
`q in M` and unit vectors `u_i in P_i`, with `u_1 in N_1`, such that

```math
 R_i u_i=-q_i u_{i-1}\qquad(2\le i\le n).
```

This is an equality channel criterion. It does not require or assert a common
eigenbasis for the operators. Other directions can remain disordered.

### Proof

For a nonzero test vector set `z_i=B_i y_i` and `x_i=||z_i||`. When `x_i>0`,
choose the **actual** scalar ratio `q_i=||R_i z_i||/x_i`, which lies in
`[ell_i,rho_i]`. When `x_i=0`, choose any allowed ratio. The reverse triangle
inequality, including its absolute value before squaring, gives

```math
 \|\mathcal A y\|^2
 \ge s^2x_1^2+\sum_{i=2}^n(x_{i-1}-q_ix_i)^2+x_n^2
 \ge L M_\beta(x)\ge L\|y\|^2.
```

Suppose equality holds for a smallest right singular vector. Every displayed
nonnegative slack then vanishes. The middle equality says that `q` minimizes
and `D_beta^-1 x` is a lowest eigenvector of `K(q)`. Irreducibility makes
this nonnegative eigenvector strictly positive, so every `x_i>0`.
Vanishing of the strong-bond slack is equivalent to `u_i=z_i/x_i` lying in
`P_i`. Vanishing of the boundary slack gives `u_1 in N_1`. Each mixed-row
slack vanishes exactly when its two nonzero vectors are oppositely aligned;
over a complex Hilbert space this follows from equality in the real part of
Cauchy-Schwarz. Thus `R_i u_i=-q_i u_(i-1)`.

Conversely take such `q` and vectors, choose the positive scalar ground
vector in normalized coordinates `x`, and put `z_i=x_i u_i`,
`y_i=B_i^-1 z_i`. Every displayed inequality becomes equality. Thus this
nonzero vector attains the robust lower bound, proving the criterion.

The sharp value theorem for matrices also follows: scalar multiples
`B_i=beta_i I`, `R_1=sI`, `R_i=-q_i I` realize every scalar minimizer in
every channel dimension.
