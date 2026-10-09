module

public import ChiralGap.SpectralAttainment
public import ChiralGap.EqualityChannels

@[expose] public section

namespace ChiralGap

/-- Explicit structural instances keep the independent model definitions stable. -/
theorem complexIdentityComposition :
    RingHomCompTriple (RingHom.id ℂ) (RingHom.id ℂ) (RingHom.id ℂ) := inferInstance

theorem complexScalarCommutes {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] :
    SMulCommClass ℂ ℂ W := inferInstance

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteDimensional ℂ V]

/-- The strong-bond bottom singular subspace in normalized site coordinates. -/
noncomputable def strongSubspace (B : V ≃ₗ[ℂ] V) (b : ℝ) : Submodule ℂ V :=
  letI : RingHomCompTriple (RingHom.id ℂ) (RingHom.id ℂ) (RingHom.id ℂ) := complexIdentityComposition
  letI : SMulCommClass ℂ ℂ V := complexScalarCommutes
  (B.toLinearMap.comp (finiteAdjoint B.toLinearMap) - ((b ^ 2 : ℝ) : ℂ) • LinearMap.id).ker

/-- The bottom right singular subspace for the first ratio. -/
noncomputable def boundarySubspace (R : V →ₗ[ℂ] V) (s : ℝ) : Submodule ℂ V :=
  letI : RingHomCompTriple (RingHom.id ℂ) (RingHom.id ℂ) (RingHom.id ℂ) := complexIdentityComposition
  letI : SMulCommClass ℂ ℂ V := complexScalarCommutes
  ((finiteAdjoint R).comp R - ((s ^ 2 : ℝ) : ℂ) • LinearMap.id).ker

lemma inverse_norm_iff_strongSubspace (B : V ≃ₗ[ℂ] V) {b : ℝ} (hb : 0 < b)
    (hB : ∀ v, b * ‖v‖ ≤ ‖B v‖) (u : V) (hu : ‖u‖ = 1) :
    ‖B.symm u‖ = 1 / b ↔ u ∈ strongSubspace B b := by
  have hmem : u ∈ strongSubspace B b ↔
      B (B.toLinearMap.adjoint u) = ((b ^ 2 : ℝ) : ℂ) • u := by
    simp [strongSubspace, finiteAdjoint, LinearMap.mem_ker, sub_eq_zero]
  rw [hmem]
  constructor
  · intro hn
    have he : ‖B (B.symm u)‖ = b * ‖B.symm u‖ := by
      rw [B.apply_symm_apply, hu, hn]
      field_simp
    have hg := (norm_attainment_iff_gram B.toLinearMap hb.le hB (B.symm u)).1 he
    have hh := congrArg B hg
    simpa using hh
  · intro hg
    have hh := congrArg B.symm hg
    have he : B.toLinearMap.adjoint (B (B.symm u)) =
        ((b ^ 2 : ℝ) : ℂ) • B.symm u := by simpa using hh
    have hn := (norm_attainment_iff_gram B.toLinearMap hb.le hB (B.symm u)).2 he
    simp only [LinearEquiv.coe_coe, B.apply_symm_apply, hu] at hn
    apply (eq_div_iff (ne_of_gt hb)).2
    nlinarith

lemma norm_iff_boundarySubspace (R : V →ₗ[ℂ] V) {s : ℝ} (hs : 0 ≤ s)
    (hR : ∀ v, s * ‖v‖ ≤ ‖R v‖) (u : V) (hu : ‖u‖ = 1) :
    ‖R u‖ = s ↔ u ∈ boundarySubspace R s := by
  have hmem : u ∈ boundarySubspace R s ↔
      R.adjoint (R u) = ((s ^ 2 : ℝ) : ℂ) • u := by
    simp [boundarySubspace, finiteAdjoint, LinearMap.mem_ker, sub_eq_zero]
  rw [hmem]
  simpa [hu] using norm_attainment_iff_gram R hs hR u

/-- The norm-attaining definition is precisely the kernel-subspace criterion
from the mathematical proof, with no simultaneous diagonalization assumption. -/
theorem equalityChannel_iff_subspaces {n : ℕ} {s L : ℝ}
    {β : Fin (n + 1) → ℝ} {ell rho : Fin n → ℝ}
    (C : GreedyCertificate s β ell rho L) (hs : 0 ≤ s) (hβ : ∀ i, 0 < β i)
    (R : Fin (n + 1) → V →ₗ[ℂ] V) (B : Fin (n + 1) → V ≃ₗ[ℂ] V)
    (hB : ∀ i v, β i * ‖v‖ ≤ ‖B i v‖) (hR : ∀ v, s * ‖v‖ ≤ ‖R 0 v‖) :
    EqualityChannel C R B ↔
      ∃ q, MinimizingFace C q ∧ ∃ u : Fin (n + 1) → V,
        (∀ i, ‖u i‖ = 1) ∧ (∀ i, u i ∈ strongSubspace (B i) (β i)) ∧
        u 0 ∈ boundarySubspace (R 0) s ∧
        ∀ j, R j.succ (u j.succ) = -(q j : ℂ) • u j.castSucc := by
  constructor
  · rintro ⟨q, hq, u, hu, hb, hf, hr⟩
    exact ⟨q, hq, u, hu, fun i => (inverse_norm_iff_strongSubspace (B i) (hβ i)
      (hB i) (u i) (hu i)).1 (hb i),
      (norm_iff_boundarySubspace (R 0) hs hR (u 0) (hu 0)).1 hf, hr⟩
  · rintro ⟨q, hq, u, hu, hb, hf, hr⟩
    exact ⟨q, hq, u, hu, fun i => (inverse_norm_iff_strongSubspace (B i) (hβ i)
      (hB i) (u i) (hu i)).2 (hb i),
      (norm_iff_boundarySubspace (R 0) hs hR (u 0) (hu 0)).2 hf, hr⟩

end ChiralGap
