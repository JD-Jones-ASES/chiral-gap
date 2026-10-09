module

public import ChiralGap.Scalar
public import ChiralGap.Variational

public section

namespace ChiralGap

/-- The lowest squared singular value for one fixed scalar chain. -/
@[expose] noncomputable def scalarGap {n : ℕ} (s : ℝ) (β : Fin (n + 1) → ℝ) (q : Fin n → ℝ) : ℝ :=
  robustMinimum s β q q

lemma scalarGap_spec {n : ℕ} (s : ℝ) (β : Fin (n + 1) → ℝ) (q : Fin n → ℝ)
    (hβ : ∀ i, 0 < β i) :
    0 < scalarGap s β q ∧
      (∀ x, scalarGap s β q * mass β x ≤ energy s q x) ∧
      ∃ x, mass β x = 1 ∧ energy s q x = scalarGap s β q := by
  obtain ⟨hp, hb, r, x, hr, hx, he⟩ := robustMinimum_spec s β q q hβ (fun _ => le_rfl)
  have heq : r = q := funext (fun i => le_antisymm (hr i).2 (hr i).1)
  subst r
  exact ⟨hp, hb q (fun _ => ⟨le_rfl, le_rfl⟩), x, hx, he⟩

lemma robustMinimum_le_scalarGap {n : ℕ} (s : ℝ) (β : Fin (n + 1) → ℝ)
    (ell rho q : Fin n → ℝ) (hβ : ∀ i, 0 < β i) (hq : Admissible ell rho q) :
    robustMinimum s β ell rho ≤ scalarGap s β q := by
  have hbox : ∀ j, ell j ≤ rho j := fun j => (hq j).1.trans (hq j).2
  obtain ⟨_, hb, _⟩ := robustMinimum_spec s β ell rho hβ hbox
  obtain ⟨_, _, x, hx, he⟩ := scalarGap_spec s β q hβ
  have hh := hb q hq x
  simpa [hx, he] using hh

/-- One of the `n + 1` ordered endpoint configurations attains the full
continuous-box optimum. Zero and fixed lower intervals are included. -/
theorem exists_one_switch_minimizer {n : ℕ} (s : ℝ) (β : Fin (n + 1) → ℝ)
    (ell rho : Fin n → ℝ) (hβ : ∀ i, 0 < β i) (hell : ∀ j, 0 ≤ ell j)
    (hbox : ∀ j, ell j ≤ rho j) :
    ∃ k : Fin (n + 1), robustMinimum s β ell rho = scalarGap s β (candidate ell rho k) := by
  obtain ⟨k, hk⟩ := Finite.exists_min (fun k : Fin (n + 1) => scalarGap s β (candidate ell rho k))
  refine ⟨k, ?_⟩
  have hle := robustMinimum_le_scalarGap s β ell rho (candidate ell rho k) hβ
    (candidate_admissible hbox k)
  apply le_antisymm hle
  by_contra h
  have hlt := lt_of_not_ge h
  let L := robustMinimum s β ell rho
  let m := scalarGap s β (candidate ell rho k)
  let t := (L + m) / 2
  have ht₁ : L < t := by dsimp [L, m, t]; linarith
  have ht₂ : t < m := by dsimp [L, m, t]; linarith
  obtain ⟨hL, hb, q, x, hq, hx, he⟩ := robustMinimum_spec s β ell rho hβ hbox
  have ht : 0 < t := lt_trans hL ht₁
  have hc : ∀ j : Fin (n + 1), ∀ y : Fin (n + 1) → ℝ, y ≠ 0 →
      t * mass β y < energy s (candidate ell rho j) y := by
    intro j y hy
    have hj := (scalarGap_spec s β (candidate ell rho j) hβ).2.1 y
    have hm : t < scalarGap s β (candidate ell rho j) := lt_of_lt_of_le ht₂ (hk j)
    exact lt_of_lt_of_le (mul_lt_mul_of_pos_right hm (mass_pos (fun i => ne_of_gt (hβ i)) hy)) hj
  have hx0 : x ≠ 0 := by intro hh; simp [hh] at hx
  have hg := energy_strict_of_candidates ht hβ hell hc q hq x hx0
  rw [hx, mul_one, he] at hg
  exact (not_lt_of_ge (le_of_lt ht₁)) hg

/-- The exact value as a finite minimum of the ordered one-switch chains. -/
theorem one_switch_value {n : ℕ} (s : ℝ) (β : Fin (n + 1) → ℝ)
    (ell rho : Fin n → ℝ) (hβ : ∀ i, 0 < β i) (hell : ∀ j, 0 ≤ ell j)
    (hbox : ∀ j, ell j ≤ rho j) :
    robustMinimum s β ell rho =
      Finset.univ.inf' Finset.univ_nonempty (fun k : Fin (n + 1) => scalarGap s β (candidate ell rho k)) := by
  obtain ⟨k, hk⟩ := exists_one_switch_minimizer s β ell rho hβ hell hbox
  apply le_antisymm
  · exact Finset.le_inf' Finset.univ_nonempty _ (fun j _ => robustMinimum_le_scalarGap s β ell rho
      (candidate ell rho j) hβ (candidate_admissible hbox j))
  · rw [hk]
    exact Finset.inf'_le _ (Finset.mem_univ k)

end ChiralGap
