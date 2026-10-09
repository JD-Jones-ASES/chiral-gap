module

public import ChiralGap.Channels

public section

namespace ChiralGap

variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- Equality in the channel estimate forces equality in every comparison step.
The conclusion includes the actual scalar optimizer, strong bonds, boundary,
and every reverse triangle comparison; no positivity of the coordinates is assumed. -/
theorem channel_equality_slacks {s L : ℝ} {β : Fin (n + 1) → ℝ}
    {ell rho : Fin n → ℝ} (hs : 0 ≤ s) (hL : 0 < L)
    (hβ : ∀ i, 0 < β i) (hbox : ∀ j, ell j ≤ rho j)
    (hscalar : ScalarLowerBound s β ell rho L)
    (R : Fin (n + 1) → V →ₗ[ℂ] V) (B : Fin (n + 1) → V ≃ₗ[ℂ] V)
    (hB : ∀ i v, β i * ‖v‖ ≤ ‖B i v‖)
    (hfirst : ∀ v, s * ‖v‖ ≤ ‖R 0 v‖)
    (hl : ∀ j v, ell j * ‖v‖ ≤ ‖R j.succ v‖)
    (hu : ∀ j v, ‖R j.succ v‖ ≤ rho j * ‖v‖)
    (y : Fin (n + 1) → V)
    (heq : channelEnergy R B y = L * channelMass y) :
    energy s (directionalRatios ell R (fun i => B i (y i)))
      (fun i => ‖B i (y i)‖) = L * mass β (fun i => ‖B i (y i)‖) ∧
    (∀ i, ‖B i (y i)‖ = β i * ‖y i‖) ∧
    ‖R 0 (B 0 (y 0))‖ = s * ‖B 0 (y 0)‖ ∧
    (∀ j : Fin n,
      ‖B j.castSucc (y j.castSucc) + R j.succ (B j.succ (y j.succ))‖ ^ 2 =
      (‖B j.castSucc (y j.castSucc)‖ - ‖R j.succ (B j.succ (y j.succ))‖) ^ 2) := by
  let z := fun i => B i (y i)
  let x := fun i => ‖z i‖
  let q := directionalRatios ell R z
  have hm := channelMass_le_mass hβ B hB y
  have hse := hscalar q (directionalRatios_admissible hbox R hl hu z) x
  have hce := scalar_energy_le_channelEnergy hs ell R B hfirst y
  have hm' : channelMass y = mass β x := by
    have hh : L * mass β x ≤ L * channelMass y := by
      calc
        _ ≤ energy s q x := hse
        _ ≤ channelEnergy R B y := hce
        _ = _ := heq
    exact le_antisymm hm ((mul_le_mul_iff_right₀ hL).mp hh)
  have hes : energy s q x = L * mass β x := by
    apply le_antisymm _ hse
    calc
      _ ≤ channelEnergy R B y := hce
      _ = L * channelMass y := heq
      _ = _ := by rw [hm']
  have hBpoint : ∀ i, ‖y i‖ ^ 2 ≤ (x i / β i) ^ 2 := by
    intro i
    apply pow_le_pow_left₀ (norm_nonneg _)
    exact (le_div_iff₀ (hβ i)).mpr (by simpa [x, z, mul_comm] using hB i (y i))
  have hBeq : ∀ i, ‖B i (y i)‖ = β i * ‖y i‖ := by
    intro i
    have hsq : ‖y i‖ ^ 2 = (x i / β i) ^ 2 :=
      (Finset.sum_eq_sum_iff_of_le (fun i _ => hBpoint i)).mp hm' i (Finset.mem_univ i)
    have hx : 0 ≤ x i / β i := div_nonneg (norm_nonneg _) (hβ i).le
    have hnorm : ‖y i‖ = x i / β i := by nlinarith [norm_nonneg (y i)]
    have hm := (eq_div_iff (hβ i).ne').mp hnorm
    simpa [x, z, mul_comm] using hm.symm
  let f := fun j : Fin n => (‖z j.castSucc‖ - ‖R j.succ (z j.succ)‖)^2
  let g := fun j : Fin n => ‖z j.castSucc + R j.succ (z j.succ)‖^2
  have hfg : ∀ j, f j ≤ g j := fun j => residual_norm_lower _ _
  have hfgsum : ∑ j, f j ≤ ∑ j, g j := Finset.sum_le_sum (fun j _ => hfg j)
  have hen : energy s q x = s^2 * ‖z 0‖^2 + ∑ j, f j + ‖z (Fin.last n)‖^2 := by
    simp only [energy, q, x, directionalRatios_mul, f]
  have hchan : channelEnergy R B y = ‖R 0 (z 0)‖^2 + ∑ j, g j + ‖z (Fin.last n)‖^2 := rfl
  have hf0 := hfirst (z 0)
  have hf0nonneg : 0 ≤ s * ‖z 0‖ := mul_nonneg hs (norm_nonneg _)
  have hf0sq : s^2 * ‖z 0‖^2 ≤ ‖R 0 (z 0)‖^2 := by
    nlinarith [norm_nonneg (R 0 (z 0))]
  have hec : energy s q x = channelEnergy R B y := by rw [hes, heq, hm']
  rw [hen, hchan] at hec
  have hfirsteq : ‖R 0 (z 0)‖ = s * ‖z 0‖ := by
    nlinarith [norm_nonneg (R 0 (z 0))]
  have hsum : ∑ j, f j = ∑ j, g j := by nlinarith
  refine ⟨hes, hBeq, hfirsteq, ?_⟩
  intro j
  exact ((Finset.sum_eq_sum_iff_of_le (fun j _ => hfg j)).mp hsum j
    (Finset.mem_univ j)).symm

end ChiralGap
