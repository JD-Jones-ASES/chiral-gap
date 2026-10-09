module

public import ChiralGap.Channels

public section

namespace ChiralGap

variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- Scalar strong bonds act identically on every channel. -/
@[expose] noncomputable def scalarStrong (β : Fin (n + 1) → ℝ) (hβ : ∀ i, 0 < β i) :
    Fin (n + 1) → V ≃ₗ[ℂ] V :=
  fun i => LinearEquiv.smulOfNeZero ℂ V (β i : ℂ) (Complex.ofReal_ne_zero.mpr (hβ i).ne')

@[simp] lemma scalarStrong_apply (β : Fin (n + 1) → ℝ) (hβ : ∀ i, 0 < β i)
    (i : Fin (n + 1)) (v : V) : scalarStrong β hβ i v = (β i : ℂ) • v := by
  simp [scalarStrong]

/-- The first ratio is `s I`; subsequent ratios are `-q_j I`. -/
@[expose] noncomputable def scalarRatio (s : ℝ) (q : Fin n → ℝ) :
    Fin (n + 1) → V →ₗ[ℂ] V :=
  Fin.cases ((s : ℂ) • LinearMap.id) (fun j => (-(q j : ℂ)) • LinearMap.id)

@[simp] lemma scalarRatio_zero (s : ℝ) (q : Fin n → ℝ) (v : V) :
    scalarRatio s q 0 v = (s : ℂ) • v := by simp [scalarRatio]

@[simp] lemma scalarRatio_succ (s : ℝ) (q : Fin n → ℝ) (j : Fin n) (v : V) :
    scalarRatio s q j.succ v = -(q j : ℂ) • v := by simp [scalarRatio]

/-- A scalar vector embedded into any unit channel. -/
@[expose] noncomputable def scalarLift (β x : Fin (n + 1) → ℝ) (u : V) : Fin (n + 1) → V :=
  fun i => ((x i / β i : ℝ) : ℂ) • u

lemma norm_real_smul_sq (r : ℝ) (u : V) (hu : ‖u‖ = 1) :
    ‖(r : ℂ) • u‖ ^ 2 = r ^ 2 := by
  simp [norm_smul, hu, Real.norm_eq_abs, sq_abs]

lemma scalarStrong_scalarLift (β x : Fin (n + 1) → ℝ) (hβ : ∀ i, 0 < β i)
    (u : V) (i : Fin (n + 1)) :
    scalarStrong β hβ i (scalarLift β x u i) = (x i : ℂ) • u := by
  rw [scalarStrong_apply, scalarLift, smul_smul]
  congr 1
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr (hβ i).ne']

/-- Equality is attained by scalar identity operators in every unit channel. -/
theorem scalar_channel_energy (β x : Fin (n + 1) → ℝ) (hβ : ∀ i, 0 < β i)
    (s : ℝ) (q : Fin n → ℝ) (u : V) (hu : ‖u‖ = 1) :
    channelEnergy (scalarRatio s q) (scalarStrong β hβ) (scalarLift β x u) =
      energy s q x := by
  unfold channelEnergy energy
  simp only [firstSite_eq_zero]
  simp only [scalarStrong_scalarLift, scalarRatio_zero, scalarRatio_succ]
  have hf : ‖(s : ℂ) • (x 0 : ℂ) • u‖ ^ 2 = s ^ 2 * x 0 ^ 2 := by
    rw [smul_smul, ← Complex.ofReal_mul, norm_real_smul_sq _ u hu]
    ring
  rw [hf, norm_real_smul_sq _ u hu]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [smul_smul, ← add_smul]
  have he : (x j.castSucc : ℂ) + -(q j : ℂ) * (x j.succ : ℂ) =
      ((x j.castSucc - q j * x j.succ : ℝ) : ℂ) := by push_cast; ring
  rw [he, norm_real_smul_sq _ u hu]

@[simp] theorem scalar_channel_mass (β x : Fin (n + 1) → ℝ)
    (u : V) (hu : ‖u‖ = 1) : channelMass (scalarLift β x u) = mass β x := by
  unfold channelMass scalarLift mass
  exact Finset.sum_congr rfl (fun i _ => norm_real_smul_sq _ u hu)

/-- The attaining construction satisfies all directional operator constraints. -/
theorem scalar_channel_constraints {β : Fin (n + 1) → ℝ} (hβ : ∀ i, 0 < β i)
    {s : ℝ} (hs : 0 ≤ s) {ell rho q : Fin n → ℝ}
    (hell : ∀ j, 0 ≤ ell j) (hq : Admissible ell rho q) :
    (∀ i (v : V), β i * ‖v‖ ≤ ‖scalarStrong β hβ i v‖) ∧
    (∀ v : V, s * ‖v‖ ≤ ‖scalarRatio s q 0 v‖) ∧
    (∀ j (v : V), ell j * ‖v‖ ≤ ‖scalarRatio s q j.succ v‖) ∧
    (∀ j (v : V), ‖scalarRatio s q j.succ v‖ ≤ rho j * ‖v‖) := by
  have hqn : ∀ j, 0 ≤ q j := fun j => le_trans (hell j) (hq j).1
  simp only [scalarStrong_apply, scalarRatio_zero, scalarRatio_succ, norm_smul,
    norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hs, abs_of_pos (hβ _), abs_of_nonneg (hqn _)]
  exact ⟨fun _ _ => le_rfl, fun _ => le_rfl,
    fun j v => mul_le_mul_of_nonneg_right (hq j).1 (norm_nonneg v),
    fun j v => mul_le_mul_of_nonneg_right (hq j).2 (norm_nonneg v)⟩

/-- Every scalar equality witness gives an equality witness in any positive channel dimension. -/
theorem channel_attainment_from_scalar [Nontrivial V]
    {β : Fin (n + 1) → ℝ} (hβ : ∀ i, 0 < β i) {s L : ℝ}
    {q : Fin n → ℝ} {x : Fin (n + 1) → ℝ}
    (hx : mass β x = 1) (he : energy s q x = L) :
    ∃ y : Fin (n + 1) → V,
      channelMass y = 1 ∧
      channelEnergy (scalarRatio s q) (scalarStrong β hβ) y = L := by
  obtain ⟨u, hu⟩ := exists_norm_eq V (show (0 : ℝ) ≤ 1 by norm_num)
  exact ⟨scalarLift β x u, (scalar_channel_mass β x u hu).trans hx,
    (scalar_channel_energy β x hβ s q u hu).trans he⟩

end ChiralGap
