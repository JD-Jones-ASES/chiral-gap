module

public import ChiralGap.Basic

public section

namespace ChiralGap

open scoped BigOperators

variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- The ordered ratio is weak bond composed with the inverse strong bond. -/
@[expose] def orderedRatio (A : V →ₗ[ℂ] V) (B : V ≃ₗ[ℂ] V) : V →ₗ[ℂ] V :=
  A.comp B.symm.toLinearMap

@[simp] theorem orderedRatio_apply_strong (A : V →ₗ[ℂ] V) (B : V ≃ₗ[ℂ] V)
    (y : V) : orderedRatio A B (B y) = A y := by simp [orderedRatio]

/-- The squared norm of the literal tall hopping map, with ratios `R = A B⁻¹`. -/
@[expose] def channelEnergy (R : Fin (n + 1) → V →ₗ[ℂ] V)
    (B : Fin (n + 1) → V ≃ₗ[ℂ] V) (y : Fin (n + 1) → V) : ℝ :=
  ‖R (firstSite n) (B (firstSite n) (y (firstSite n)))‖ ^ 2 +
    ∑ j : Fin n, ‖B j.castSucc (y j.castSucc) + R j.succ (B j.succ (y j.succ))‖ ^ 2
    + ‖B (Fin.last n) (y (Fin.last n))‖ ^ 2

/-- Squared Hilbert norm, written as a sum so arbitrary channel dimension is explicit. -/
@[expose] def channelMass (y : Fin (n + 1) → V) : ℝ := ∑ i, ‖y i‖ ^ 2

/-- Actual directional ratios, including vectors on which the strong-bond image vanishes. -/
@[expose] noncomputable def directionalRatios (ell : Fin n → ℝ)
    (R : Fin (n + 1) → V →ₗ[ℂ] V) (z : Fin (n + 1) → V) (j : Fin n) : ℝ :=
  if ‖z j.succ‖ = 0 then ell j else ‖R j.succ (z j.succ)‖ / ‖z j.succ‖

lemma directionalRatios_mul (ell : Fin n → ℝ)
    (R : Fin (n + 1) → V →ₗ[ℂ] V) (z : Fin (n + 1) → V) (j : Fin n) :
    directionalRatios ell R z j * ‖z j.succ‖ = ‖R j.succ (z j.succ)‖ := by
  unfold directionalRatios
  split_ifs with h
  · have hz : z j.succ = 0 := norm_eq_zero.mp h
    simp [hz]
  · exact div_mul_cancel₀ _ h

lemma directionalRatios_admissible {ell rho : Fin n → ℝ}
    (hbox : ∀ j, ell j ≤ rho j)
    (R : Fin (n + 1) → V →ₗ[ℂ] V)
    (hl : ∀ j v, ell j * ‖v‖ ≤ ‖R j.succ v‖)
    (hu : ∀ j v, ‖R j.succ v‖ ≤ rho j * ‖v‖)
    (z : Fin (n + 1) → V) : Admissible ell rho (directionalRatios ell R z) := by
  intro j
  unfold directionalRatios
  split_ifs with h
  · exact ⟨le_rfl, hbox j⟩
  · have hp : 0 < ‖z j.succ‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h)
    exact ⟨(le_div_iff₀ hp).2 (hl j _), (div_le_iff₀ hp).2 (hu j _)⟩

omit [NormedSpace ℂ V] in
/-- Reverse triangle inequality in precisely the squared form needed by the chain. -/
lemma residual_norm_lower (u v : V) : (‖u‖ - ‖v‖) ^ 2 ≤ ‖u + v‖ ^ 2 := by
  have h := abs_norm_sub_norm_le u (-v)
  simp only [norm_neg, sub_neg_eq_add] at h
  nlinarith [sq_abs (‖u‖ - ‖v‖), sq_nonneg (‖u + v‖ - |‖u‖ - ‖v‖|),
    abs_nonneg (‖u‖ - ‖v‖), norm_nonneg (u + v)]

/-- The exact directional comparison, valid without commutation or diagonalization. -/
theorem scalar_energy_le_channelEnergy {s : ℝ} (hs : 0 ≤ s)
    (ell : Fin n → ℝ) (R : Fin (n + 1) → V →ₗ[ℂ] V)
    (B : Fin (n + 1) → V ≃ₗ[ℂ] V)
    (hfirst : ∀ v, s * ‖v‖ ≤ ‖R 0 v‖) (y : Fin (n + 1) → V) :
    energy s (directionalRatios ell R (fun i => B i (y i)))
      (fun i => ‖B i (y i)‖) ≤ channelEnergy R B y := by
  unfold energy channelEnergy
  simp only [firstSite_eq_zero]
  have hf : s ^ 2 * ‖B 0 (y 0)‖ ^ 2 ≤ ‖R 0 (B 0 (y 0))‖ ^ 2 := by
    have := hfirst (B 0 (y 0))
    have hn := norm_nonneg (R 0 (B 0 (y 0)))
    have hp : 0 ≤ s * ‖B 0 (y 0)‖ := mul_nonneg hs (norm_nonneg _)
    nlinarith
  have he : (∑ j : Fin n,
      (‖B j.castSucc (y j.castSucc)‖ -
        directionalRatios ell R (fun i => B i (y i)) j * ‖B j.succ (y j.succ)‖)^2) ≤
      ∑ j : Fin n, ‖B j.castSucc (y j.castSucc) + R j.succ (B j.succ (y j.succ))‖^2 := by
    apply Finset.sum_le_sum
    intro j _
    rw [directionalRatios_mul]
    exact residual_norm_lower _ _
  linarith

lemma channelMass_le_mass {β : Fin (n + 1) → ℝ}
    (hβ : ∀ i, 0 < β i) (B : Fin (n + 1) → V ≃ₗ[ℂ] V)
    (hB : ∀ i v, β i * ‖v‖ ≤ ‖B i v‖) (y : Fin (n + 1) → V) :
    channelMass y ≤ mass β (fun i => ‖B i (y i)‖) := by
  unfold channelMass mass
  apply Finset.sum_le_sum
  intro i _
  have h : ‖y i‖ ≤ ‖B i (y i)‖ / β i :=
    (le_div_iff₀ (hβ i)).2 (by simpa [mul_comm] using hB i (y i))
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

/-- Sharp transfer of any scalar box bound to arbitrary complex channel operators. -/
theorem channel_lower_bound {s L : ℝ} {β : Fin (n + 1) → ℝ}
    {ell rho : Fin n → ℝ} (hs : 0 ≤ s) (hL : 0 ≤ L)
    (hβ : ∀ i, 0 < β i) (hbox : ∀ j, ell j ≤ rho j)
    (hscalar : ScalarLowerBound s β ell rho L)
    (R : Fin (n + 1) → V →ₗ[ℂ] V) (B : Fin (n + 1) → V ≃ₗ[ℂ] V)
    (hB : ∀ i v, β i * ‖v‖ ≤ ‖B i v‖)
    (hfirst : ∀ v, s * ‖v‖ ≤ ‖R 0 v‖)
    (hl : ∀ j v, ell j * ‖v‖ ≤ ‖R j.succ v‖)
    (hu : ∀ j v, ‖R j.succ v‖ ≤ rho j * ‖v‖)
    (y : Fin (n + 1) → V) : L * channelMass y ≤ channelEnergy R B y := by
  let z := fun i => B i (y i)
  calc
    L * channelMass y ≤ L * mass β (fun i => ‖z i‖) :=
      mul_le_mul_of_nonneg_left (channelMass_le_mass hβ B hB y) hL
    _ ≤ energy s (directionalRatios ell R z) (fun i => ‖z i‖) :=
      hscalar _ (directionalRatios_admissible hbox R hl hu z) _
    _ ≤ channelEnergy R B y := scalar_energy_le_channelEnergy hs ell R B hfirst y

end ChiralGap
