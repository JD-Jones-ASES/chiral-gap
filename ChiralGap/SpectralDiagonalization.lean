module

public import ChiralGap.Spectral

public section

namespace ChiralGap

open Module

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F]

/-- The same chiral block operator equipped with the Hilbert direct-sum norm. -/
@[expose] noncomputable def chiralHilbert (A : E →ₗ[ℂ] F) :
    WithLp 2 (F × E) →ₗ[ℂ] WithLp 2 (F × E) :=
  (WithLp.linearEquiv 2 ℂ (F × E)).symm.toLinearMap.comp
    ((chiral A).comp (WithLp.linearEquiv 2 ℂ (F × E)).toLinearMap)

/-- The finite chiral Hamiltonian is genuinely Hermitian. -/
theorem chiralHilbert_isSymmetric (A : E →ₗ[ℂ] F) :
    (chiralHilbert A).IsSymmetric := by
  intro x y
  simp [chiralHilbert, WithLp.prod_inner_apply, A.adjoint_inner_left,
    A.adjoint_inner_right, add_comm]

/-- An actual real eigenbasis rules out nontrivial Jordan blocks, so geometric
spectral multiplicities in the chiral bridge are also algebraic multiplicities. -/
theorem chiral_eigenbasis (A : E →ₗ[ℂ] F) :
    ∃ (b : Basis (Fin (finrank ℂ (WithLp 2 (F × E)))) ℂ (F × E))
      (t : Fin (finrank ℂ (WithLp 2 (F × E))) → ℝ),
      ∀ i, chiral A (b i) = (t i : ℂ) • b i := by
  let h := chiralHilbert_isSymmetric A
  let b := (h.eigenvectorBasis rfl).toBasis
  let e := WithLp.linearEquiv 2 ℂ (F × E)
  refine ⟨b.map e, h.eigenvalues rfl, ?_⟩
  intro i
  have hi := h.apply_eigenvectorBasis rfl i
  change chiral A (e (b i)) = (h.eigenvalues rfl i : ℂ) • e (b i)
  calc
    _ = e (chiralHilbert A (b i)) := rfl
    _ = e ((h.eigenvalues rfl i : ℂ) • b i) := congrArg e hi
    _ = _ := e.map_smul _ _

end ChiralGap
