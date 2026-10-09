module

public import Mathlib

public section

set_option maxHeartbeats 800000

namespace ChiralGap

open Module Module.End

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F]

/-- A typed adjoint wrapper fixes the structural instances in the independent model. -/
@[expose] noncomputable def finiteAdjoint (A : E →ₗ[ℂ] F) : F →ₗ[ℂ] E := A.adjoint

/-- The actual chiral block operator `[0 A; A† 0]`. -/
@[expose] noncomputable def chiral (A : E →ₗ[ℂ] F) : (F × E) →ₗ[ℂ] (F × E) :=
  (A.comp (LinearMap.snd ℂ F E)).prod ((finiteAdjoint A).comp (LinearMap.fst ℂ F E))

@[simp] theorem chiral_apply (A : E →ₗ[ℂ] F) (z : F × E) :
    chiral A z = (A z.2, A.adjoint z.1) := rfl

/-- Nonzero chiral eigenspaces are explicitly isomorphic to squared Gram eigenspaces. -/
noncomputable def chiralEigenspaceEquiv (A : E →ₗ[ℂ] F) {μ : ℂ} (hμ : μ ≠ 0) :
    Module.End.eigenspace (chiral A) μ ≃ₗ[ℂ] Module.End.eigenspace (A.adjoint.comp A) (μ ^ 2) where
  toFun z := ⟨z.val.2, by
    have hz := Module.End.mem_eigenspace_iff.mp z.property
    have h1 : A z.val.2 = μ • z.val.1 := congrArg Prod.fst hz
    have h2 : A.adjoint z.val.1 = μ • z.val.2 := congrArg Prod.snd hz
    rw [Module.End.mem_eigenspace_iff]
    simp only [LinearMap.comp_apply, h1, map_smul, h2, smul_smul, pow_two]⟩
  invFun y := ⟨(μ⁻¹ • A y.val, y.val), by
    rw [Module.End.mem_eigenspace_iff]
    have hy := Module.End.mem_eigenspace_iff.mp y.property
    ext
    · simp [hμ]
    · simp only [chiral_apply, map_smul, Prod.smul_snd, LinearMap.comp_apply] at *
      rw [hy, smul_smul]
      field_simp⟩
  left_inv z := by
    apply Subtype.ext
    have hz := congrArg Prod.fst (Module.End.mem_eigenspace_iff.mp z.property)
    change A z.val.2 = μ • z.val.1 at hz
    ext <;> simp [hz, hμ]
  right_inv y := by rfl
  map_add' x y := by rfl
  map_smul' a x := by rfl

/-- Kernel vectors are precisely the adjoint zero modes together with hopping zero modes. -/
theorem chiral_ker (A : E →ₗ[ℂ] F) :
    (chiral A).ker = A.adjoint.ker.prod A.ker := by
  ext z
  simp only [LinearMap.mem_ker, chiral_apply, Prod.mk_eq_zero, Submodule.mem_prod]
  exact and_comm

/-- Identification of the zero modes for an injective hopping operator. -/
noncomputable def chiralKernelEquiv (A : E →ₗ[ℂ] F) (hA : Function.Injective A) :
    (chiral A).ker ≃ₗ[ℂ] A.adjoint.ker where
  toFun z := ⟨z.val.1, congrArg Prod.snd z.property⟩
  invFun x := ⟨(x.val, 0), by simp [LinearMap.mem_ker]⟩
  left_inv z := by
    apply Subtype.ext
    have hz : A z.val.2 = 0 := congrArg Prod.fst z.property
    have hy : z.val.2 = 0 := hA (by simpa using hz)
    exact Prod.ext rfl hy.symm
  right_inv x := rfl
  map_add' x y := rfl
  map_smul' a x := rfl

/-- An injective rectangular hopping map has exactly the excess number of zero modes. -/
theorem chiral_zero_multiplicity (A : E →ₗ[ℂ] F) (hA : Function.Injective A) :
    finrank ℂ (chiral A).ker = finrank ℂ F - finrank ℂ E := by
  rw [(chiralKernelEquiv A hA).finrank_eq]
  have h := A.adjoint.finrank_range_add_finrank_ker
  have hr : finrank ℂ A.range = finrank ℂ E := LinearMap.finrank_range_of_inj hA
  rw [A.finrank_range_adjoint, hr] at h
  omega

/-- The two signs have exactly the same eigenspace dimension, including repeated values. -/
theorem chiral_signed_multiplicity (A : E →ₗ[ℂ] F) {μ : ℂ} (hμ : μ ≠ 0) :
    finrank ℂ (Module.End.eigenspace (chiral A) μ) =
      finrank ℂ (Module.End.eigenspace (chiral A) (-μ)) := by
  rw [(chiralEigenspaceEquiv A hμ).finrank_eq,
    (chiralEigenspaceEquiv A (neg_ne_zero.mpr hμ)).finrank_eq, neg_sq]

/-- The spectral bridge is an equivalence for every nonzero complex energy. -/
theorem chiral_eigenvalue_iff_squared (A : E →ₗ[ℂ] F) {μ : ℂ} (hμ : μ ≠ 0) :
    Module.End.HasEigenvalue (chiral A) μ ↔
      Module.End.HasEigenvalue (A.adjoint.comp A) (μ ^ 2) := by
  rw [Module.End.hasEigenvalue_iff, Module.End.hasEigenvalue_iff]
  constructor
  · intro he hz
    apply he
    apply Submodule.finrank_eq_zero.mp
    rw [(chiralEigenspaceEquiv A hμ).finrank_eq, hz, finrank_bot]
  · intro he hz
    apply he
    apply Submodule.finrank_eq_zero.mp
    rw [← (chiralEigenspaceEquiv A hμ).finrank_eq, hz, finrank_bot]

/-- Every indexed nonzero singular value contributes an actual positive chiral eigenvalue. -/
theorem chiral_has_singularValue (A : E →ₗ[ℂ] F) (i : ℕ)
    (hi : i < finrank ℂ E) (hσ : A.singularValues i ≠ 0) :
    Module.End.HasEigenvalue (chiral A) (A.singularValues i : ℂ) := by
  have hμ : (A.singularValues i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hσ
  have hg := A.hasEigenvalue_adjoint_comp_self_sq_singularValues hi
  have he := chiralEigenspaceEquiv A hμ
  rw [Module.End.hasEigenvalue_iff] at hg ⊢
  intro hz
  have hzdim : finrank ℂ (Module.End.eigenspace (A.adjoint.comp A)
      ((A.singularValues i : ℂ)^2)) = 0 := by
    rw [← he.finrank_eq, hz, finrank_bot]
  apply hg
  apply Submodule.finrank_eq_zero.mp
  simpa using hzdim

/-- The negative of every nonzero singular value is also an actual eigenvalue. -/
theorem chiral_has_neg_singularValue (A : E →ₗ[ℂ] F) (i : ℕ)
    (hi : i < finrank ℂ E) (hσ : A.singularValues i ≠ 0) :
    Module.End.HasEigenvalue (chiral A) (-(A.singularValues i : ℂ)) := by
  have hp := chiral_has_singularValue A i hi hσ
  have hd := chiral_signed_multiplicity A (Complex.ofReal_ne_zero.mpr hσ)
  rw [Module.End.hasEigenvalue_iff] at hp ⊢
  intro hz
  apply hp
  apply Submodule.finrank_eq_zero.mp
  rw [hd, hz, finrank_bot]

/-- Complete nonzero spectral description; no extra complex energies occur. -/
theorem chiral_nonzero_spectrum (A : E →ₗ[ℂ] F) {μ : ℂ} (hμ : μ ≠ 0) :
    Module.End.HasEigenvalue (chiral A) μ ↔
      ∃ i : ℕ, i < finrank ℂ E ∧
        (μ = (A.singularValues i : ℂ) ∨ μ = -(A.singularValues i : ℂ)) := by
  constructor
  · intro he
    have hg : Module.End.HasEigenvalue (A.adjoint.comp A) (μ ^ 2) := by
      rw [Module.End.hasEigenvalue_iff] at he ⊢
      intro hz
      apply he
      apply Submodule.finrank_eq_zero.mp
      rw [(chiralEigenspaceEquiv A hμ).finrank_eq, hz, finrank_bot]
    obtain ⟨i, hi⟩ := A.isSymmetric_adjoint_comp_self.exists_eigenvalues_eq rfl hg
    have hsq : (A.singularValues i : ℂ) ^ 2 = μ ^ 2 := by
      rw [← Complex.ofReal_pow, A.sq_singularValues_fin rfl i]
      exact hi
    refine ⟨i, i.isLt, ?_⟩
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq.symm with hp | hn
    · exact Or.inl hp
    · exact Or.inr hn
  · rintro ⟨i, hi, he | he⟩
    · have hσ : A.singularValues i ≠ 0 := by intro hz; apply hμ; simp [he, hz]
      rw [he]
      exact chiral_has_singularValue A i hi hσ
    · have hσ : A.singularValues i ≠ 0 := by intro hz; apply hμ; simp [he, hz]
      rw [he]
      exact chiral_has_neg_singularValue A i hi hσ

/-- Gram eigenvalues obey the same literal norm lower bound as the hopping map. -/
theorem gram_eigenvalue_lower_bound (A : E →ₗ[ℂ] F) {L t : ℝ}
    (hbound : ∀ y, L * ‖y‖ ^ 2 ≤ ‖A y‖ ^ 2)
    (ht : Module.End.HasEigenvalue (A.adjoint.comp A) (t : ℂ)) : L ≤ t := by
  obtain ⟨y, hy, hne⟩ := ht.exists_hasEigenvector
  have he : A.adjoint (A y) = (t : ℂ) • y :=
    Module.End.mem_eigenspace_iff.mp hy
  have hn : 0 < ‖y‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hne)
  have hi := congrArg Complex.re (A.adjoint_inner_right y (A y))
  rw [he] at hi
  simp only [inner_smul_right, inner_self_eq_norm_sq_to_K,
    Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im] at hi
  norm_num [RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_pow] at hi
  have hh := hbound y
  nlinarith

/-- All singular values below the domain dimension are bounded by the excitation gap. -/
theorem singularValue_gap (A : E →ₗ[ℂ] F) {L : ℝ} (_hL : 0 ≤ L)
    (hbound : ∀ y, L * ‖y‖ ^ 2 ≤ ‖A y‖ ^ 2)
    (i : ℕ) (hi : i < finrank ℂ E) : Real.sqrt L ≤ A.singularValues i := by
  have hg := A.hasEigenvalue_adjoint_comp_self_sq_singularValues hi
  have hg' : Module.End.HasEigenvalue (A.adjoint.comp A)
      ((A.singularValues i ^ 2 : ℝ) : ℂ) := by
    convert! hg using 1
    push_cast
    rfl
  have h := gram_eigenvalue_lower_bound A hbound hg'
  exact (Real.sqrt_le_iff).2 ⟨A.singularValues_nonneg i, h⟩

/-- Every nonzero real chiral energy has absolute value at least `sqrt L`. -/
theorem chiral_energy_gap (A : E →ₗ[ℂ] F) {L t : ℝ} (_hL : 0 ≤ L)
    (hbound : ∀ y, L * ‖y‖ ^ 2 ≤ ‖A y‖ ^ 2) (ht : t ≠ 0)
    (he : Module.End.HasEigenvalue (chiral A) (t : ℂ)) : Real.sqrt L ≤ |t| := by
  have hg : Module.End.HasEigenvalue (A.adjoint.comp A) ((t ^ 2 : ℝ) : ℂ) := by
    rw [Module.End.hasEigenvalue_iff] at he ⊢
    intro hz
    apply he
    apply Submodule.finrank_eq_zero.mp
    rw [(chiralEigenspaceEquiv A (Complex.ofReal_ne_zero.mpr ht)).finrank_eq]
    simpa using congrArg (fun S : Submodule ℂ E => finrank ℂ S) hz
  have h := gram_eigenvalue_lower_bound A hbound hg
  apply (Real.sqrt_le_iff).2
  exact ⟨abs_nonneg _, by simpa only [sq_abs] using h⟩

end ChiralGap
