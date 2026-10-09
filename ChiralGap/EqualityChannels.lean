module

public import ChiralGap.Equality
public import ChiralGap.ChannelSharpness
public import ChiralGap.ChannelEquality
public import ChiralGap.GreedyExistence

@[expose] public section

noncomputable section

namespace ChiralGap

variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- A basis-free equality channel. The strong and boundary conditions say that the
unit vectors attain the corresponding least singular bounds. -/
def EqualityChannel {s : ℝ} {β : Fin (n + 1) → ℝ}
    {ell rho : Fin n → ℝ} {L : ℝ} (C : GreedyCertificate s β ell rho L)
    (R : Fin (n + 1) → V →ₗ[ℂ] V) (B : Fin (n + 1) → V ≃ₗ[ℂ] V) : Prop :=
  ∃ q : Fin n → ℝ, MinimizingFace C q ∧
    ∃ u : Fin (n + 1) → V,
      (∀ i, ‖u i‖ = 1) ∧ (∀ i, ‖(B i).symm (u i)‖ = 1 / β i) ∧
      ‖R 0 (u 0)‖ = s ∧ ∀ j, R j.succ (u j.succ) = -(q j : ℂ) • u j.castSucc

/-- Equality in the actual arbitrary-channel energy, with a nonzero test vector. -/
def AttainsChannel (R : Fin (n + 1) → V →ₗ[ℂ] V)
    (B : Fin (n + 1) → V ≃ₗ[ℂ] V) (L : ℝ) : Prop :=
  ∃ y : Fin (n + 1) → V, y ≠ 0 ∧ channelEnergy R B y = L * channelMass y

/-- Lift a scalar ground vector into prescribed unit channel directions. -/
def channelGroundLift (B : Fin (n + 1) → V ≃ₗ[ℂ] V)
    (x : Fin (n + 1) → ℝ) (u : Fin (n + 1) → V) : Fin (n + 1) → V :=
  fun i => (B i).symm ((x i : ℂ) • u i)

@[simp] theorem strong_channelGroundLift (B : Fin (n + 1) → V ≃ₗ[ℂ] V)
    (x : Fin (n + 1) → ℝ) (u : Fin (n + 1) → V) (i : Fin (n + 1)) :
    B i (channelGroundLift B x u i) = (x i : ℂ) • u i := by
  simp [channelGroundLift]

theorem channelGroundLift_mass {β : Fin (n + 1) → ℝ}
    (B : Fin (n + 1) → V ≃ₗ[ℂ] V) (x : Fin (n + 1) → ℝ)
    (u : Fin (n + 1) → V) (hB : ∀ i, ‖(B i).symm (u i)‖ = 1 / β i) :
    channelMass (channelGroundLift B x u) = mass β x := by
  unfold channelMass channelGroundLift mass
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, norm_smul, hB]
  simp only [Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

theorem channelGroundLift_energy {s : ℝ} {q : Fin n → ℝ}
    (R : Fin (n + 1) → V →ₗ[ℂ] V) (B : Fin (n + 1) → V ≃ₗ[ℂ] V)
    (x : Fin (n + 1) → ℝ) (u : Fin (n + 1) → V)
    (hu : ∀ i, ‖u i‖ = 1) (hf : ‖R 0 (u 0)‖ = s)
    (hR : ∀ j, R j.succ (u j.succ) = -(q j : ℂ) • u j.castSucc) :
    channelEnergy R B (channelGroundLift B x u) = energy s q x := by
  unfold channelEnergy energy
  simp only [firstSite_eq_zero]
  simp only [strong_channelGroundLift]
  have hfirst : ‖R 0 ((x 0 : ℂ) • u 0)‖ ^ 2 = s ^ 2 * x 0 ^ 2 := by
    rw [map_smul, norm_smul, hf]
    simp only [Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  rw [hfirst, norm_real_smul_sq _ _ (hu _)]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul, hR, smul_smul, ← add_smul]
  have hc : (x j.castSucc : ℂ) + (x j.succ : ℂ) * -(q j : ℂ) =
      ((x j.castSucc - q j * x j.succ : ℝ) : ℂ) := by push_cast; ring
  rw [hc, norm_real_smul_sq _ _ (hu _)]

/-- A complete equality channel suffices for exact attainment. -/
theorem equalityChannel_attains {s : ℝ} {β : Fin (n + 1) → ℝ}
    {ell rho : Fin n → ℝ} {L : ℝ} (C : GreedyCertificate s β ell rho L)
    (hell : ∀ j, 0 < ell j)
    (R : Fin (n + 1) → V →ₗ[ℂ] V) (B : Fin (n + 1) → V ≃ₗ[ℂ] V)
    (hc : EqualityChannel C R B) : AttainsChannel R B L := by
  obtain ⟨q, hq, u, hu, hB, hf, hR⟩ := hc
  refine ⟨channelGroundLift B (C.groundVector q) u, ?_, ?_⟩
  · intro hz
    have hh := congrArg (B 0) (congrFun hz 0)
    simp only [strong_channelGroundLift, C.groundVector_zero, Complex.ofReal_one,
      one_smul, Pi.zero_apply, map_zero] at hh
    have hunit := hu 0
    simp [hh] at hunit
  · rw [channelGroundLift_energy R B _ u hu hf hR, channelGroundLift_mass B _ u hB]
    exact C.face_attains hell hq

section InnerProduct

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]

/-- The reverse-triangle equality in a complex Hilbert space forces opposite alignment. -/
theorem antiparallel_of_norm_add_sq_eq {u v : W} (hu : 0 < ‖u‖)
    (h : ‖u + v‖ ^ 2 = (‖u‖ - ‖v‖) ^ 2) :
    v = (-(‖v‖ / ‖u‖) : ℂ) • u := by
  have hi := norm_add_sq (𝕜 := ℂ) u v
  have hs := norm_add_sq (𝕜 := ℂ) (((‖v‖ / ‖u‖ : ℝ) : ℂ) • u) v
  have hn : 0 ≤ ‖v‖ / ‖u‖ := div_nonneg (norm_nonneg v) (le_of_lt hu)
  simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hn,
    inner_smul_left, Complex.conj_ofReal] at hs
  change ‖u + v‖ ^ 2 = ‖u‖ ^ 2 + 2 * (inner ℂ u v).re + ‖v‖ ^ 2 at hi
  change ‖((‖v‖ / ‖u‖ : ℝ) : ℂ) • u + v‖ ^ 2 =
    (‖v‖ / ‖u‖ * ‖u‖) ^ 2 +
      2 * (((‖v‖ / ‖u‖ : ℝ) : ℂ) * inner ℂ u v).re + ‖v‖ ^ 2 at hs
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hs
  have he : ‖((‖v‖ / ‖u‖ : ℝ) : ℂ) • u + v‖ ^ 2 = 0 := by
    have hdiv : ‖v‖ / ‖u‖ * ‖u‖ = ‖v‖ := div_mul_cancel₀ _ (ne_of_gt hu)
    nlinarith
  have hz := norm_eq_zero.mp (sq_eq_zero_iff.mp he)
  have hv := eq_neg_of_add_eq_zero_right hz
  simpa using hv

/-- Normalize a nonzero strong-bond image to its channel direction. -/
def normalizedChannel (B : Fin (n + 1) → W ≃ₗ[ℂ] W)
    (y : Fin (n + 1) → W) (i : Fin (n + 1)) : W :=
  ((1 / ‖B i (y i)‖ : ℝ) : ℂ) • B i (y i)

theorem normalizedChannel_norm (B : Fin (n + 1) → W ≃ₗ[ℂ] W)
    (y : Fin (n + 1) → W) {i : Fin (n + 1)} (h : 0 < ‖B i (y i)‖) :
    ‖normalizedChannel B y i‖ = 1 := by
  simp [normalizedChannel, norm_smul, ne_of_gt h]

/-- Exact slacks produce the geometric equality channel, including opposite alignment. -/
theorem equalityChannel_of_slacks {s : ℝ} {β : Fin (n + 1) → ℝ}
    {ell rho : Fin n → ℝ} {L : ℝ} (C : GreedyCertificate s β ell rho L)
    (hβ : ∀ i, 0 < β i) (hell : ∀ j, 0 < ell j)
    (R : Fin (n + 1) → W →ₗ[ℂ] W) (B : Fin (n + 1) → W ≃ₗ[ℂ] W)
    {y : Fin (n + 1) → W} (hy : y ≠ 0)
    (hq : Admissible ell rho (directionalRatios ell R (fun i => B i (y i))))
    (he : energy s (directionalRatios ell R (fun i => B i (y i)))
      (fun i => ‖B i (y i)‖) = L * mass β (fun i => ‖B i (y i)‖))
    (hB : ∀ i, β i * ‖y i‖ = ‖B i (y i)‖)
    (hf : ‖R 0 (B 0 (y 0))‖ = s * ‖B 0 (y 0)‖)
    (hr : ∀ j : Fin n,
      ‖B j.castSucc (y j.castSucc) + R j.succ (B j.succ (y j.succ))‖ ^ 2 =
        (‖B j.castSucc (y j.castSucc)‖ - ‖R j.succ (B j.succ (y j.succ))‖) ^ 2) :
    EqualityChannel C R B := by
  have hx : (fun i => ‖B i (y i)‖) ≠ (0 : Fin (n + 1) → ℝ) := by
    intro hz
    apply hy
    funext i
    have hi : ‖B i (y i)‖ = 0 := congrFun hz i
    exact (B i).injective (by simpa using norm_eq_zero.mp hi)
  have hp := C.equality_positive hell hq hx (fun i => norm_nonneg _) he
  refine ⟨directionalRatios ell R (fun i => B i (y i)),
    (C.attains_iff_face hell hq).1 ⟨_, hx, he⟩, normalizedChannel B y,
    fun i => normalizedChannel_norm B y (hp i), ?_, ?_, ?_⟩
  · intro i
    simp only [normalizedChannel, map_smul, LinearEquiv.symm_apply_apply, norm_smul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos zero_lt_one (hp i))]
    apply (eq_div_iff (ne_of_gt (hβ i))).2
    have hh := hB i
    field_simp [ne_of_gt (hp i)]
    nlinarith
  · simp only [normalizedChannel, map_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (div_pos zero_lt_one (hp 0)), hf]
    field_simp [ne_of_gt (hp 0)]
  · intro j
    have halign := antiparallel_of_norm_add_sq_eq (hp j.castSucc) (hr j)
    simp only [normalizedChannel, map_smul]
    rw [halign]
    simp only [smul_smul]
    congr 1
    simp only [directionalRatios, ne_of_gt (hp j.succ), ↓reduceIte]
    push_cast
    field_simp

/-- Necessary and sufficient equality-channel criterion for arbitrary complex
Hilbert channels. The scalar face is the complete minimizing face. -/
theorem channel_attains_iff_equalityChannel {s L : ℝ} {β : Fin (n + 1) → ℝ}
    {ell rho : Fin n → ℝ} (C : GreedyCertificate s β ell rho L)
    (hs : 0 ≤ s) (hL : 0 < L) (hβ : ∀ i, 0 < β i)
    (hell : ∀ j, 0 < ell j) (hbox : ∀ j, ell j ≤ rho j)
    (R : Fin (n + 1) → W →ₗ[ℂ] W) (B : Fin (n + 1) → W ≃ₗ[ℂ] W)
    (hB : ∀ i v, β i * ‖v‖ ≤ ‖B i v‖)
    (hfirst : ∀ v, s * ‖v‖ ≤ ‖R 0 v‖)
    (hl : ∀ j v, ell j * ‖v‖ ≤ ‖R j.succ v‖)
    (hu : ∀ j v, ‖R j.succ v‖ ≤ rho j * ‖v‖) :
    AttainsChannel R B L ↔ EqualityChannel C R B := by
  constructor
  · rintro ⟨y, hy, he⟩
    obtain ⟨hscl, hstr, hbd, hrow⟩ := channel_equality_slacks hs hL hβ hbox
      (C.lower_bound (fun j => le_of_lt (hell j))) R B hB hfirst hl hu y he
    exact equalityChannel_of_slacks C hβ hell R B hy
      (directionalRatios_admissible hbox R hl hu _) hscl (fun i => (hstr i).symm) hbd hrow
  · exact equalityChannel_attains C hell R B

/-- The full equality classification at the actual attained robust scalar minimum.
No pivot certificate or equality vector is assumed: the pivots are constructed. -/
theorem channel_equality_classification (s : ℝ) (β : Fin (n + 1) → ℝ)
    (ell rho : Fin n → ℝ) (hs : 0 ≤ s) (hβ : ∀ i, 0 < β i)
    (hell : ∀ j, 0 < ell j) (hbox : ∀ j, ell j ≤ rho j)
    (R : Fin (n + 1) → W →ₗ[ℂ] W) (B : Fin (n + 1) → W ≃ₗ[ℂ] W)
    (hB : ∀ i v, β i * ‖v‖ ≤ ‖B i v‖)
    (hfirst : ∀ v, s * ‖v‖ ≤ ‖R 0 v‖)
    (hl : ∀ j v, ell j * ‖v‖ ≤ ‖R j.succ v‖)
    (hu : ∀ j v, ‖R j.succ v‖ ≤ rho j * ‖v‖) :
    ∃ C : GreedyCertificate s β ell rho (robustMinimum s β ell rho),
      (∀ q, ScalarMinimizer s β ell rho q ↔ MinimizingFace C q) ∧
      (AttainsChannel R B (robustMinimum s β ell rho) ↔ EqualityChannel C R B) := by
  obtain ⟨C⟩ := greedyCertificate_exists s β ell rho hβ hell hbox
  exact ⟨C, scalarMinimizer_iff_face hβ hell C,
    channel_attains_iff_equalityChannel C hs (robustMinimum_spec s β ell rho hβ hbox).1
      hβ hell hbox R B hB hfirst hl hu⟩

end InnerProduct

end ChiralGap
