# Sources and scope of the chiral-gap result

Date: **2026-10-08**. This is a bounded intake and literature assessment,
not a priority determination or an external specialist review.

## Supplied material and verification boundary

JD supplied *Exact robust gaps in finite chiral chains: Two scalar
certificates for arbitrary matrix disorder*, a thirteen-page research draft
dated 8 October 2026, and attributed its ideas to GPT 6 Pro. Its SHA-256, checked on 8 October 2026, is

```text
47f18375cf797059b550ebb0ef3de0c56384b71396b88e5fd690893a0209b387
```

The supplied PDF is the source for the two-certificate reduction, boundary
threshold, matrix-channel comparison and one-switch interval theorem.
The written proof preserves that provenance and separates the original
results from the positive-lower-bound extensions.

No Lean source, exported proof object, compiler log or checker configuration
was supplied with the PDF. Its reports of Lean, NanoDa and con-ron success
have **not been independently verified**. They are source claims, not verification evidence for this repository.
The machine-verification boundary for this development is stated in the README.

## The closest interval-matrix comparison

[Hladík, *Eigenvalues of symmetric tridiagonal interval matrices revisited*,
arXiv:1704.03670v2](https://arxiv.org/html/1704.03670v2) was checked in full
text, particularly Sections 2–6. Proposition 5 reduces the outermost
eigenvalue extrema to endpoint matrices. Intermediate eigenvalues require
additional sign-pattern analysis; the paper treats sign invariancy, its
failure and disjoint eigenvalue ranges. It does not state the draft's
one-switch optimizer theorem.

The draft's distinction based only on correlated Gram entries is incomplete.
The following direct comparison fixes the relevant eigenvalue index.
Order scalar physical coordinates as

```math
(u_0,y_1,u_1,y_2,u_2,\ldots,y_n,u_n).
```

After a diagonal phase/sign change, the chiral Hamiltonian is a symmetric
tridiagonal matrix with zero diagonal and off-diagonal magnitudes

```math
(s\beta_1,\ \beta_1,\ q_2\beta_2,\ \beta_2,\ldots,
q_n\beta_n,\ \beta_n).
```

Thus the scalar Hamiltonian itself is an entrywise interval matrix: uncertain
weak bonds give independent intervals, and fixed bonds give degenerate
intervals. Its gap is its **nth largest** eigenvalue, equivalently its
**(n+2)nd smallest**, since the tall hopping factor has rank n and the
Hamiltonian has exactly n positive eigenvalues, one zero and n negative
eigenvalues. Hladík's outermost-eigenvalue formula therefore does not directly
give this gap, but his broader interval-matrix framework does contain the
scalar problem. With s>0 and every lower weak-bond bound positive, all
off-diagonals are positive and the Jacobi eigenvalues are simple; allowed
zero bonds require the corresponding reducible/limit cases.

The plausible additional contribution is the **explicit one-switch
optimizer structure, its two-configuration collapse when cuts are allowed,
sharp boundary/equality information, and an exact arbitrary-channel lift**.
The Gram correlation is useful for the proof, but is not by itself a
separation from interval-matrix theory. Whether the structural reduction
already occurs elsewhere remains unresolved.

## Standard ingredients and physical context

| Primary source | What was checked | Relationship to this investigation |
|---|---|---|
| [Higham, *The Power of Bidiagonal Matrices*, arXiv:2311.06609v1](https://arxiv.org/html/2311.06609v1), published in *Electronic Journal of Linear Algebra* 40 (2024), [DOI](https://doi.org/10.13001/ela.2024.8297) | Full-text Sections 2–3, including Lemma 3 and Theorems 6–7, and the later total-nonnegativity discussion | The inverse-product formula, phase removal and singular-value simplicity are established matrix theory. The checked results concern structure, perturbation and computation, not the asserted one-switch uncertainty optimum. |
| [Hladík, *An Overview of Polynomially Computable Characteristics of Special Interval Matrices*, arXiv:1711.08732v1](https://arxiv.org/html/1711.08732v1) | Full-text Sections 2–5, especially Theorem 9 | Exact smallest-singular-value endpoints for square inverse-nonnegative interval families already explain saturation of a zero-boundary square bidiagonal suffix. That standard consequence is not the research contribution. The boundary-pinned tall factor is a different remaining issue. |
| [Graf and Shapiro, *The Bulk-Edge Correspondence for Disordered Chiral Chains*, arXiv:1801.09487v1](https://arxiv.org/html/1801.09487v1), [DOI](https://doi.org/10.1007/s00220-018-3247-0) | Full-text model, Assumptions 1–2, main index theorem and spectral-gap discussion | This is a matrix-channel chiral model on infinite and half-infinite chains, with deterministic localization assumptions and bulk/edge indices. It supports the physical context; its checked theorem is not a finite minimax spectral-gap formula. |
| [Jezequel, Tauber and Delplace, *Estimating bulk and edge topological indices in finite open chiral chains*, arXiv:2203.17099v2](https://arxiv.org/html/2203.17099v2), [DOI](https://doi.org/10.1063/5.0096720) | Full-text assumptions, index definitions and main finite-size theorem | The theorem assumes a short-range bulk Hamiltonian with a bulk spectral gap and controls finite open-chain indices. An open chain may still have edge states near zero. It does not derive the local-constraint minimax gap studied here. |
| [Yamamoto, *Equality conditions for lower bounds on the smallest singular value of a bidiagonal matrix*](https://www.sciencedirect.com/science/article/abs/pii/S0096300307011046), *Applied Mathematics and Computation* 200 (2008), 254–260, DOI 10.1016/j.amc.2007.11.005 | Publisher abstract, introduction and exposed section excerpts; **not the complete paper** | Equality in named lower bounds for a fixed square bidiagonal matrix is a close supporting topic. These accessible portions do not establish or rule out overlap with the uncertainty optimizer classification. |
| [Wang and Zhang, *The block lower bounds for the smallest singular value*](https://www.tandfonline.com/doi/full/10.1080/00207160412331296616), *International Journal of Computer Mathematics* 82 (2005), 313–319 | Publisher abstract and bibliographic record only; **not full text** | The abstract describes lower bounds using block comparison matrices under conditions. It prevents claiming block comparison itself as new, but is insufficient for a theorem-level comparison with sharp noncommuting-channel attainment. The publisher's online date is 25 January 2007; the volume year is 2005. |

Further primary-source leads found but not cleared at theorem level are
[Hladík, Daney and Tsigaridas, *Bounds on Real Eigenvalues and Singular Values
of Interval Matrices*](https://epubs.siam.org/doi/10.1137/090753991)
(publisher abstract and references inspected) and
[Ahn and Chen, *Exact Maximum Singular Value Calculation of an Interval
Matrix*](https://ksp.etri.re.kr/ksp/article/read?id=42212)
(the first author's institutional repository abstract inspected;
DOI 10.1109/TAC.2006.890475). Both include general interval singular-value
questions. No complete comparison with their proofs was performed.

The search covered combinations of bidiagonal singular values, interval
matrices, correlated tridiagonal uncertainty, one-switch optimization and
finite chiral/SSH gap disorder. It was a targeted primary-source search,
not a systematic bibliographic census. Failure to locate the exact theorem
does not establish absence from the literature.


## Result and limitations

The research contribution under consideration is the exact one-switch optimum,
the point-or-edge minimizing set with positive lower bounds, and the sharp
noncommuting-channel transfer with complete equality channels. The standard
bidiagonal identities and chiral spectral pairing support that result.
Worldwide priority and external specialist review remain unestablished.

The point-or-edge claim requires strictly positive weak lower bounds. With
zero lower bounds, the value theorem still holds, but larger minimizing
faces can occur. Closing a chain into a cycle invalidates the general
endpoint principle. These theorems do not concern interacting many-body
gaps, arbitrary on-site disorder, or an infinite-volume bulk-edge theorem.
