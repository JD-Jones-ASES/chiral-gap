module

public import ChiralGap.GreedyChain
public import ChiralGap.Equality
public import ChiralGap.Value

@[expose] public section
noncomputable section
namespace ChiralGap

/-- The variational optimum always supplies the greedy certificate when every
lower endpoint is positive. The certificate is a conclusion, not a hypothesis. -/
theorem greedyCertificate_exists {n : ℕ} (s : ℝ) (β : Fin (n + 1) → ℝ)
    (ell rho : Fin n → ℝ) (hβ : ∀ i, 0 < β i)
    (hl : ∀ j, 0 < ell j) (horder : ∀ j, ell j ≤ rho j) :
    Nonempty (GreedyCertificate s β ell rho (robustMinimum s β ell rho)) := by
  obtain ⟨hpos, hbound, q, x, hq, hx, he⟩ := robustMinimum_spec s β ell rho hβ horder
  have hN : ∀ r, Admissible ell rho r →
      ChainNonneg (1 + s ^ 2 - robustMinimum s β ell rho / β 0 ^ 2)
        (fun j : Fin n => 1 - robustMinimum s β ell rho / β j.succ ^ 2) r := by
    intro r hr y
    rw [chainForm_eq_energy_sub_mass]
    exact sub_nonneg.mpr (hbound r hr y)
  have hxn : x ≠ 0 := by
    intro h
    rw [h, mass_zero] at hx
    norm_num at hx
  have hz : chainForm n (1 + s ^ 2 - robustMinimum s β ell rho / β 0 ^ 2)
        (fun j : Fin n => 1 - robustMinimum s β ell rho / β j.succ ^ 2) q x = 0 := by
    rw [chainForm_eq_energy_sub_mass, hx, he]
    ring
  obtain ⟨p, hp0, hstep, hp, hlast⟩ := exists_greedy_pivots n hl horder hN ⟨q, x, hq, hxn, hz⟩
  exact ⟨⟨p, hp0, hstep, hp, hlast⟩⟩

/-- The actual scalar optimizer set, expressed using the fixed-chain Rayleigh minimum. -/
def ScalarMinimizer {n : ℕ} (s : ℝ) (β : Fin (n + 1) → ℝ)
    (ell rho q : Fin n → ℝ) : Prop :=
  Admissible ell rho q ∧ scalarGap s β q = robustMinimum s β ell rho

lemma scalarMinimizer_iff_face {n : ℕ} {s : ℝ} {β : Fin (n + 1) → ℝ}
    {ell rho : Fin n → ℝ} (hβ : ∀ i, 0 < β i) (hl : ∀ j, 0 < ell j)
    (C : GreedyCertificate s β ell rho (robustMinimum s β ell rho))
    (q : Fin n → ℝ) : ScalarMinimizer s β ell rho q ↔ MinimizingFace C q := by
  constructor
  · rintro ⟨hq, he⟩
    apply (C.attains_iff_face hl hq).1
    obtain ⟨_, _, x, hx, hxE⟩ := scalarGap_spec s β q hβ
    have hxn : x ≠ 0 := by intro h; simp [h] at hx
    exact ⟨x, hxn, by rw [hxE, hx, mul_one, he]⟩
  · intro hf
    refine ⟨hf.1, le_antisymm ?_ ?_⟩
    · obtain ⟨x, hx, he⟩ := (C.attains_iff_face hl hf.1).2 hf
      have hb := (scalarGap_spec s β q hβ).2.1 x
      have hm := mass_pos (fun i => ne_of_gt (hβ i)) hx
      rw [he] at hb
      exact (mul_le_mul_iff_left₀ hm).mp hb
    · exact robustMinimum_le_scalarGap s β ell rho q hβ hf.1

/-- The complete optimizer classification at the attained robust minimum.
All hypotheses concern only the model data; existence of the pivots is proved. -/
theorem scalar_optimizer_classification {n : ℕ} (s : ℝ) (β : Fin (n + 1) → ℝ)
    (ell rho : Fin n → ℝ) (hβ : ∀ i, 0 < β i)
    (hl : ∀ j, 0 < ell j) (horder : ∀ j, ell j ≤ rho j) :
    ∃ C : GreedyCertificate s β ell rho (robustMinimum s β ell rho),
      (∀ q, ScalarMinimizer s β ell rho q ↔ MinimizingFace C q) ∧
      (∀ i j : Fin n, C.pivot i.castSucc = 1 → C.pivot j.castSucc = 1 → i = j) := by
  obtain ⟨C⟩ := greedyCertificate_exists s β ell rho hβ hl horder
  refine ⟨C, scalarMinimizer_iff_face hβ hl C, ?_⟩
  intro i j hi hj
  exact C.tie_unique hβ (robustMinimum_spec s β ell rho hβ horder).1 hi hj

/-- Every scalar optimizer set is one ordered endpoint vertex or one full
transition interval. Fixed intervals are included in both alternatives. -/
theorem scalar_minimizers_vertex_or_edge {n : ℕ} (s : ℝ) (β : Fin (n + 1) → ℝ)
    (ell rho : Fin n → ℝ) (hβ : ∀ i, 0 < β i)
    (hl : ∀ j, 0 < ell j) (horder : ∀ j, ell j ≤ rho j) :
    (∃ k : Fin (n + 1), ∀ q, ScalarMinimizer s β ell rho q ↔ q = candidate ell rho k) ∨
    (∃ k : Fin n, ∀ q, ScalarMinimizer s β ell rho q ↔
      Admissible ell rho q ∧
        (∀ j, j < k → q j = ell j) ∧ (∀ j, k < j → q j = rho j)) := by
  classical
  obtain ⟨C⟩ := greedyCertificate_exists s β ell rho hβ hl horder
  have hL := (robustMinimum_spec s β ell rho hβ horder).1
  have hface := scalarMinimizer_iff_face hβ hl C
  by_cases ht : ∃ k : Fin n, C.pivot k.castSucc = 1
  · obtain ⟨k, hk⟩ := ht
    right
    refine ⟨k, fun q => ?_⟩
    rw [hface q]
    have hbefore {j : Fin n} (hj : j < k) : 1 < C.pivot j.castSucc := by
      by_contra hn
      have hh := C.pivot_below_one hβ hL (Fin.castSucc_lt_castSucc_iff.mpr hj) (le_of_not_gt hn)
      linarith
    have hafter {j : Fin n} (hj : k < j) : C.pivot j.castSucc < 1 :=
      C.pivot_below_one hβ hL (Fin.castSucc_lt_castSucc_iff.mpr hj) (le_of_eq hk)
    constructor
    · rintro ⟨hq, hr⟩
      exact ⟨hq, fun j hj => (hr j).1 (hbefore hj), fun j hj => (hr j).2 (hafter hj)⟩
    · rintro ⟨hq, hb, ha⟩
      refine ⟨hq, fun j => ?_⟩
      rcases lt_trichotomy j k with hj | hj | hj
      · exact ⟨fun _ => hb j hj, fun hh => by have := hbefore hj; linarith⟩
      · subst j; simp [EndpointRule, hk]
      · exact ⟨fun hh => by have := hafter hj; linarith, fun _ => ha j hj⟩
  · left
    obtain ⟨k, hk⟩ := exists_one_switch_minimizer s β ell rho hβ (fun j => (hl j).le) horder
    have hkc : ScalarMinimizer s β ell rho (candidate ell rho k) :=
      ⟨candidate_admissible horder k, hk.symm⟩
    have hkr := (hface _).1 hkc
    refine ⟨k, fun q => ?_⟩
    constructor
    · intro hq
      have hqr := (hface q).1 hq
      ext j
      have hne : C.pivot j.castSucc ≠ 1 := fun hh => ht ⟨j, hh⟩
      exact ((endpointRule_iff_greedy hne).1 (hqr.2 j)).trans
        ((endpointRule_iff_greedy hne).1 (hkr.2 j)).symm
    · intro hq
      simpa [hq] using hkc

end ChiralGap
