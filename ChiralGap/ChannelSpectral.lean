module

public import ChiralGap.ChannelSharpness
public import ChiralGap.Spectral
public import ChiralGap.SpectralAttainment
public import ChiralGap.Variational

public section

namespace ChiralGap

open Module

variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- A Hilbert direct sum of `m` complex channel spaces. -/
abbrev ChannelSpace (m : ℕ) (V : Type*) := PiLp 2 (fun _ : Fin m => V)

/-- The tall hopping map as an actual linear operator on finite complex Hilbert spaces. -/
@[expose] noncomputable def hopping (R : Fin (n + 1) → V →ₗ[ℂ] V)
    (B : Fin (n + 1) → V ≃ₗ[ℂ] V) :
    ChannelSpace (n + 1) V →ₗ[ℂ] ChannelSpace (n + 2) V where
  toFun y := WithLp.toLp 2 (Fin.cases (R (firstSite n) (B (firstSite n) (y (firstSite n))))
    (Fin.lastCases (B (Fin.last n) (y (Fin.last n)))
      (fun j => B j.castSucc (y j.castSucc) + R j.succ (B j.succ (y j.succ)))))
  map_add' y z := by
    apply PiLp.ext
    intro k
    refine Fin.cases ?_ (fun i => Fin.lastCases ?_ (fun j => ?_) i) k <;>
      simp [map_add, add_add_add_comm, -Fin.succ_last]
  map_smul' a y := by
    apply PiLp.ext
    intro k
    refine Fin.cases ?_ (fun i => Fin.lastCases ?_ (fun j => ?_) i) k <;>
      simp [map_smul, smul_add, -Fin.succ_last]

@[simp] lemma hopping_first (R : Fin (n + 1) → V →ₗ[ℂ] V)
    (B : Fin (n + 1) → V ≃ₗ[ℂ] V) (y : ChannelSpace (n + 1) V) :
    hopping R B y 0 = R 0 (B 0 (y 0)) := rfl

@[simp] lemma hopping_edge (R : Fin (n + 1) → V →ₗ[ℂ] V)
    (B : Fin (n + 1) → V ≃ₗ[ℂ] V) (y : ChannelSpace (n + 1) V) (j : Fin n) :
    hopping R B y j.castSucc.succ =
      B j.castSucc (y j.castSucc) + R j.succ (B j.succ (y j.succ)) := by
  simp [hopping, -Fin.succ_last]

@[simp] lemma hopping_last (R : Fin (n + 1) → V →ₗ[ℂ] V)
    (B : Fin (n + 1) → V ≃ₗ[ℂ] V) (y : ChannelSpace (n + 1) V) :
    hopping R B y (Fin.last (n + 1)) = B (Fin.last n) (y (Fin.last n)) := by
  change hopping R B y (Fin.last n).succ = _
  simp [hopping, -Fin.succ_last]

/-- The first physical row is `A₀ y₀`, with the ratio composition in its required order. -/
@[simp] theorem hopping_physical_first (A : Fin (n + 1) → V →ₗ[ℂ] V)
    (B : Fin (n + 1) → V ≃ₗ[ℂ] V) (y : ChannelSpace (n + 1) V) :
    hopping (fun i => orderedRatio (A i) (B i)) B y 0 = A 0 (y 0) := by simp

/-- Every interior physical row is `Bⱼ yⱼ + Aⱼ₊₁ yⱼ₊₁`. -/
@[simp] theorem hopping_physical_edge (A : Fin (n + 1) → V →ₗ[ℂ] V)
    (B : Fin (n + 1) → V ≃ₗ[ℂ] V) (y : ChannelSpace (n + 1) V) (j : Fin n) :
    hopping (fun i => orderedRatio (A i) (B i)) B y j.castSucc.succ =
      B j.castSucc (y j.castSucc) + A j.succ (y j.succ) := by simp

/-- The scalar expression used for transfer is exactly the operator norm squared. -/
theorem hopping_norm_sq (R : Fin (n + 1) → V →ₗ[ℂ] V)
    (B : Fin (n + 1) → V ≃ₗ[ℂ] V) (y : ChannelSpace (n + 1) V) :
    ‖hopping R B y‖ ^ 2 = channelEnergy R B y := by
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_succ]
  rw [Fin.sum_univ_castSucc]
  simp only [hopping_first, hopping_edge]
  change _ + (_ + ‖hopping R B y (Fin.last (n + 1))‖^2) = _
  rw [hopping_last]
  simp [channelEnergy, add_assoc]

omit [InnerProductSpace ℂ V] in
@[simp] theorem channelSpace_norm_sq (y : ChannelSpace (n + 1) V) :
    ‖y‖ ^ 2 = channelMass y := PiLp.norm_sq_eq_of_L2 _ _

variable [FiniteDimensional ℂ V]

/-- Dimension counts retain the number of channels exactly. -/
theorem channelSpace_finrank (m : ℕ) :
    finrank ℂ (ChannelSpace m V) = m * finrank ℂ V := by
  rw [(WithLp.linearEquiv 2 ℂ (Fin m → V)).finrank_eq,
    Module.finrank_pi_fintype]
  simp

omit [FiniteDimensional ℂ V] in
/-- The lower-triangular end of the open chain makes the hopping map injective. -/
theorem hopping_injective (R : Fin (n + 1) → V →ₗ[ℂ] V)
    (B : Fin (n + 1) → V ≃ₗ[ℂ] V) : Function.Injective (hopping R B) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro y hy
  have hl : y (Fin.last n) = 0 := by
    have h := congrArg (fun z : ChannelSpace (n + 2) V => z (Fin.last (n + 1))) hy
    simp only [hopping_last, PiLp.zero_apply] at h
    exact (B (Fin.last n)).injective (by simpa using h)
  have he : ∀ j : Fin n, y j.succ = 0 → y j.castSucc = 0 := by
    intro j hj
    have h := congrArg (fun z : ChannelSpace (n + 2) V => z j.castSucc.succ) hy
    simp [hopping_edge, hj] at h
    exact h
  apply PiLp.ext
  intro i
  exact Fin.reverseInduction hl he i

/-- The zero eigenspace has exactly one channel block, with no additional zero modes. -/
theorem hopping_chiral_zero_multiplicity (R : Fin (n + 1) → V →ₗ[ℂ] V)
    (B : Fin (n + 1) → V ≃ₗ[ℂ] V) :
    finrank ℂ (chiral (hopping R B)).ker = finrank ℂ V := by
  rw [chiral_zero_multiplicity _ (hopping_injective R B),
    channelSpace_finrank, channelSpace_finrank]
  simp only [Nat.add_mul]
  omega

omit [FiniteDimensional ℂ V] in
/-- Unconditional transfer of the actual attained robust scalar minimum. -/
theorem robust_hopping_bound {s : ℝ} {β : Fin (n + 1) → ℝ}
    {ell rho : Fin n → ℝ} (hs : 0 ≤ s) (hβ : ∀ i, 0 < β i)
    (hbox : ∀ j, ell j ≤ rho j)
    (R : Fin (n + 1) → V →ₗ[ℂ] V) (B : Fin (n + 1) → V ≃ₗ[ℂ] V)
    (hB : ∀ i v, β i * ‖v‖ ≤ ‖B i v‖)
    (hfirst : ∀ v, s * ‖v‖ ≤ ‖R 0 v‖)
    (hl : ∀ j v, ell j * ‖v‖ ≤ ‖R j.succ v‖)
    (hu : ∀ j v, ‖R j.succ v‖ ≤ rho j * ‖v‖)
    (y : ChannelSpace (n + 1) V) :
    robustMinimum s β ell rho * ‖y‖ ^ 2 ≤ ‖hopping R B y‖ ^ 2 := by
  obtain ⟨hpos, hscalar, _⟩ := robustMinimum_spec s β ell rho hβ hbox
  rw [hopping_norm_sq, channelSpace_norm_sq]
  exact channel_lower_bound hs hpos.le hβ hbox hscalar R B hB hfirst hl hu y

/-- The finite chiral Hamiltonian has the physical square-root excitation bound. -/
theorem robust_chiral_gap {s t : ℝ} {β : Fin (n + 1) → ℝ}
    {ell rho : Fin n → ℝ} (hs : 0 ≤ s) (hβ : ∀ i, 0 < β i)
    (hbox : ∀ j, ell j ≤ rho j)
    (R : Fin (n + 1) → V →ₗ[ℂ] V) (B : Fin (n + 1) → V ≃ₗ[ℂ] V)
    (hB : ∀ i v, β i * ‖v‖ ≤ ‖B i v‖)
    (hfirst : ∀ v, s * ‖v‖ ≤ ‖R 0 v‖)
    (hl : ∀ j v, ell j * ‖v‖ ≤ ‖R j.succ v‖)
    (hu : ∀ j v, ‖R j.succ v‖ ≤ rho j * ‖v‖)
    (ht : t ≠ 0) (he : Module.End.HasEigenvalue (chiral (hopping R B)) (t : ℂ)) :
    Real.sqrt (robustMinimum s β ell rho) ≤ |t| := by
  apply chiral_energy_gap _ (robustMinimum_spec s β ell rho hβ hbox).1.le
    (robust_hopping_bound hs hβ hbox R B hB hfirst hl hu) ht he

omit [FiniteDimensional ℂ V] in
/-- The robust norm bound is attained, for every nonzero finite complex channel space. -/
theorem robust_hopping_attained [Nontrivial V]
    (s : ℝ) (β : Fin (n + 1) → ℝ) (ell rho : Fin n → ℝ)
    (hβ : ∀ i, 0 < β i) (hbox : ∀ j, ell j ≤ rho j) :
    ∃ q : Fin n → ℝ, Admissible ell rho q ∧
      ∃ y : ChannelSpace (n + 1) V,
        ‖y‖ ^ 2 = 1 ∧
        ‖hopping (scalarRatio s q) (scalarStrong β hβ) y‖ ^ 2 =
          robustMinimum s β ell rho := by
  obtain ⟨_, _, q, x, hq, hx, he⟩ := robustMinimum_spec s β ell rho hβ hbox
  obtain ⟨y, hym, hye⟩ := channel_attainment_from_scalar (V := V) hβ hx he
  refine ⟨q, hq, WithLp.toLp 2 y, ?_, ?_⟩
  · rw [channelSpace_norm_sq]
    exact hym
  · rw [hopping_norm_sq]
    exact hye


/-- Both signs of the exact square-root gap occur in an admissible model, in every
positive complex channel dimension. -/
theorem robust_chiral_sharpness [Nontrivial V]
    (s : ℝ) (β : Fin (n + 1) → ℝ) (ell rho : Fin n → ℝ)
    (hs : 0 ≤ s) (hβ : ∀ i, 0 < β i)
    (hell : ∀ j, 0 ≤ ell j) (hbox : ∀ j, ell j ≤ rho j) :
    ∃ q : Fin n → ℝ, Admissible ell rho q ∧
      Module.End.HasEigenvalue
        (chiral (hopping (V := V) (scalarRatio s q) (scalarStrong β hβ)))
        (Real.sqrt (robustMinimum s β ell rho) : ℂ) ∧
      Module.End.HasEigenvalue
        (chiral (hopping (V := V) (scalarRatio s q) (scalarStrong β hβ)))
        (-(Real.sqrt (robustMinimum s β ell rho) : ℂ)) := by
  obtain ⟨q, hq, y, hym, hye⟩ := robust_hopping_attained (V := V) s β ell rho hβ hbox
  obtain ⟨hB, hf, hl, hu⟩ := scalar_channel_constraints (V := V) hβ hs hell hq
  let A := hopping (V := V) (scalarRatio s q) (scalarStrong β hβ)
  have hbound : ∀ z, robustMinimum s β ell rho * ‖z‖^2 ≤ ‖A z‖^2 :=
    robust_hopping_bound hs hβ hbox _ _ hB hf hl hu
  have heq : ‖A y‖^2 = robustMinimum s β ell rho * ‖y‖^2 := by
    rw [hym, mul_one]
    exact hye
  have hgram := gram_eq_of_norm_attainment A hbound y heq
  have hy : y ≠ 0 := by intro hy; simp [hy] at hym
  have hL := (robustMinimum_spec s β ell rho hβ hbox).1
  have hsqrt : (Real.sqrt (robustMinimum s β ell rho) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hL).ne'
  have hg : Module.End.HasEigenvalue (A.adjoint.comp A)
      ((Real.sqrt (robustMinimum s β ell rho) : ℂ)^2) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hL.le]
    exact Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr hgram, hy⟩
  refine ⟨q, hq, (chiral_eigenvalue_iff_squared A hsqrt).mpr hg, ?_⟩
  apply (chiral_eigenvalue_iff_squared A (neg_ne_zero.mpr hsqrt)).mpr
  simpa only [neg_sq] using hg


/-- Fully constrained sharpness: admissible operators, in every positive channel
dimension, have both signs of the robust gap as actual chiral energies. -/
theorem robust_chiral_sharpness_constrained [Nontrivial V]
    (s : ℝ) (β : Fin (n + 1) → ℝ) (ell rho : Fin n → ℝ)
    (hs : 0 ≤ s) (hβ : ∀ i, 0 < β i)
    (hell : ∀ j, 0 ≤ ell j) (hbox : ∀ j, ell j ≤ rho j) :
    ∃ (R : Fin (n + 1) → V →ₗ[ℂ] V) (B : Fin (n + 1) → V ≃ₗ[ℂ] V),
      (∀ i v, β i * ‖v‖ ≤ ‖B i v‖) ∧
      (∀ v, s * ‖v‖ ≤ ‖R 0 v‖) ∧
      (∀ j v, ell j * ‖v‖ ≤ ‖R j.succ v‖) ∧
      (∀ j v, ‖R j.succ v‖ ≤ rho j * ‖v‖) ∧
      Module.End.HasEigenvalue (chiral (hopping R B))
        (Real.sqrt (robustMinimum s β ell rho) : ℂ) ∧
      Module.End.HasEigenvalue (chiral (hopping R B))
        (-(Real.sqrt (robustMinimum s β ell rho) : ℂ)) := by
  obtain ⟨q, hq, hp, hn⟩ := robust_chiral_sharpness (V := V) s β ell rho hs hβ hell hbox
  obtain ⟨hB, hf, hl, hu⟩ := scalar_channel_constraints (V := V) hβ hs hell hq
  exact ⟨scalarRatio s q, scalarStrong β hβ, hB, hf, hl, hu, hp, hn⟩


end ChiralGap
