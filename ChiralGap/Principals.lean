module

public import ChiralGap.ChannelSpectral
public import ChiralGap.EqualityChannels
public import ChiralGap.EqualitySubspaces

@[expose] public section

namespace ChiralGap

variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteDimensional ℂ V]

/-- The robust constant is sharp within the stated uncertainty class in every
positive complex channel dimension. The same witness satisfies every constraint. -/
theorem robust_channel_sharpness [Nontrivial V]
    (s : ℝ) (β : Fin (n + 1) → ℝ) (ell rho : Fin n → ℝ)
    (hs : 0 ≤ s) (hβ : ∀ i, 0 < β i) (hell : ∀ j, 0 ≤ ell j)
    (hbox : ∀ j, ell j ≤ rho j) :
    ∃ (R : Fin (n + 1) → V →ₗ[ℂ] V) (B : Fin (n + 1) → V ≃ₗ[ℂ] V),
      (∀ i v, β i * ‖v‖ ≤ ‖B i v‖) ∧
      (∀ v, s * ‖v‖ ≤ ‖R 0 v‖) ∧
      (∀ j v, ell j * ‖v‖ ≤ ‖R j.succ v‖) ∧
      (∀ j v, ‖R j.succ v‖ ≤ rho j * ‖v‖) ∧
      ∃ y : ChannelSpace (n + 1) V, ‖y‖ ^ 2 = 1 ∧
        ‖hopping R B y‖ ^ 2 = robustMinimum s β ell rho := by
  obtain ⟨q, hq, y, hy, he⟩ := robust_hopping_attained (V := V) s β ell rho hβ hbox
  obtain ⟨hB, hf, hl, hu⟩ := scalar_channel_constraints (V := V) hβ hs hell hq
  exact ⟨scalarRatio s q, scalarStrong β hβ, hB, hf, hl, hu, y, hy, he⟩

/-- The full nonzero complex spectrum of the actual chain consists exactly of
the two signs of its `(n + 1) * dim(V)` singular values. -/
theorem hopping_nonzero_spectrum (R : Fin (n + 1) → V →ₗ[ℂ] V)
    (B : Fin (n + 1) → V ≃ₗ[ℂ] V) {μ : ℂ} (hμ : μ ≠ 0) :
    Module.End.HasEigenvalue (chiral (hopping R B)) μ ↔
      ∃ i : ℕ, i < (n + 1) * Module.finrank ℂ V ∧
        (μ = ((hopping R B).singularValues i : ℂ) ∨
          μ = -((hopping R B).singularValues i : ℂ)) := by
  simpa only [channelSpace_finrank] using chiral_nonzero_spectrum (hopping R B) hμ

/-- The square-root excitation bound controls every nonzero complex eigenvalue;
there is no hidden hypothesis restricting the spectrum to real inputs. -/
theorem robust_chiral_complex_gap {s : ℝ} {β : Fin (n + 1) → ℝ}
    {ell rho : Fin n → ℝ} (hs : 0 ≤ s) (hβ : ∀ i, 0 < β i)
    (hbox : ∀ j, ell j ≤ rho j)
    (R : Fin (n + 1) → V →ₗ[ℂ] V) (B : Fin (n + 1) → V ≃ₗ[ℂ] V)
    (hB : ∀ i v, β i * ‖v‖ ≤ ‖B i v‖)
    (hfirst : ∀ v, s * ‖v‖ ≤ ‖R 0 v‖)
    (hl : ∀ j v, ell j * ‖v‖ ≤ ‖R j.succ v‖)
    (hu : ∀ j v, ‖R j.succ v‖ ≤ rho j * ‖v‖)
    {μ : ℂ} (hμ : μ ≠ 0) (he : Module.End.HasEigenvalue (chiral (hopping R B)) μ) :
    Real.sqrt (robustMinimum s β ell rho) ≤ ‖μ‖ := by
  obtain ⟨i, hi, hm | hm⟩ := (chiral_nonzero_spectrum (hopping R B) hμ).1 he
  · rw [hm, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ((hopping R B).singularValues_nonneg i)]
    exact singularValue_gap _ (robustMinimum_spec s β ell rho hβ hbox).1.le
      (robust_hopping_bound hs hβ hbox R B hB hfirst hl hu) i hi
  · rw [hm, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ((hopping R B).singularValues_nonneg i)]
    exact singularValue_gap _ (robustMinimum_spec s β ell rho hβ hbox).1.le
      (robust_hopping_bound hs hβ hbox R B hB hfirst hl hu) i hi

/-- The complete matrix equality-channel theorem in singular-subspace form.
Every object in the statement is determined by the original model data. -/
theorem matrix_equality_criterion (s : ℝ) (β : Fin (n + 1) → ℝ)
    (ell rho : Fin n → ℝ) (hs : 0 ≤ s) (hβ : ∀ i, 0 < β i)
    (hell : ∀ j, 0 < ell j) (hbox : ∀ j, ell j ≤ rho j)
    (R : Fin (n + 1) → V →ₗ[ℂ] V) (B : Fin (n + 1) → V ≃ₗ[ℂ] V)
    (hB : ∀ i v, β i * ‖v‖ ≤ ‖B i v‖)
    (hfirst : ∀ v, s * ‖v‖ ≤ ‖R 0 v‖)
    (hl : ∀ j v, ell j * ‖v‖ ≤ ‖R j.succ v‖)
    (hu : ∀ j v, ‖R j.succ v‖ ≤ rho j * ‖v‖) :
    AttainsChannel R B (robustMinimum s β ell rho) ↔
      ∃ q, ScalarMinimizer s β ell rho q ∧ ∃ u : Fin (n + 1) → V,
        (∀ i, ‖u i‖ = 1) ∧ (∀ i, u i ∈ strongSubspace (B i) (β i)) ∧
        u 0 ∈ boundarySubspace (R 0) s ∧
        ∀ j, R j.succ (u j.succ) = -(q j : ℂ) • u j.castSucc := by
  obtain ⟨C⟩ := greedyCertificate_exists s β ell rho hβ hell hbox
  rw [channel_attains_iff_equalityChannel C hs
    (robustMinimum_spec s β ell rho hβ hbox).1 hβ hell hbox R B hB hfirst hl hu,
    equalityChannel_iff_subspaces C hs hβ R B hB hfirst]
  simp only [scalarMinimizer_iff_face hβ hell C]

end ChiralGap
