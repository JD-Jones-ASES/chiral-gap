module

public import ChiralGap.Value

public section

namespace ChiralGap

/-- Saturate every weak link except the first, which is cut. -/
def firstCut {n : ℕ} (rho : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  Fin.cons 0 (Fin.tail rho)

lemma chainPositive_of_two {n : ℕ} {a : ℝ} {d rho : Fin (n + 1) → ℝ}
    (hd : ∀ j, d j < 1) (hu : ChainPositive a d rho)
    (hc : ChainPositive a d (firstCut rho)) :
    ∀ q, Admissible 0 rho q → ChainPositive a d q := by
  intro q hq
  by_cases ha1 : a < 1
  · exact chainPositive_of_upper (n + 1) ha1 hd (fun _ => le_rfl) hu q hq
  · have ha : 0 < a := chainPositive_first hu
    apply (chainPositive_schur ha).2
    have ht : ChainPositive (d 0) (Fin.tail d) (Fin.tail rho) := by
      simpa [firstCut] using (chainPositive_schur ha).1 hc
    have htail := chainPositive_of_upper n (hd 0) (fun j => hd j.succ)
      (fun _ => le_rfl) ht (Fin.tail q) (fun j => hq j.succ)
    apply chainPositive_mono (h := htail)
    have hm := update_lower ha (le_of_not_gt ha1) (show (0 : ℝ) ≤ 0 from le_rfl) (hq 0).1
    simpa using hm

lemma energy_strict_of_two {n : ℕ} {s L : ℝ}
    {β : Fin (n + 2) → ℝ} {rho : Fin (n + 1) → ℝ}
    (hL : 0 < L) (hβ : ∀ i, 0 < β i)
    (hu : ∀ x, x ≠ 0 → L * mass β x < energy s rho x)
    (hc : ∀ x, x ≠ 0 → L * mass β x < energy s (firstCut rho) x) :
    ∀ q, Admissible 0 rho q → ∀ x, x ≠ 0 → L * mass β x < energy s q x := by
  have hd : ∀ j : Fin (n + 1), 1 - L / β j.succ ^ 2 < 1 := by
    intro j
    have hp := div_pos hL (sq_pos_of_pos (hβ j.succ))
    linarith
  have h := chainPositive_of_two hd
    (a := 1 + s ^ 2 - L / β 0 ^ 2)
    (fun x hx => by rw [chainForm_eq_energy_sub_mass]; exact sub_pos.mpr (hu x hx))
    (fun x hx => by rw [chainForm_eq_energy_sub_mass]; exact sub_pos.mpr (hc x hx))
  intro q hq x hx
  have hh := h q hq x hx
  rw [chainForm_eq_energy_sub_mass] at hh
  exact sub_pos.mp hh

lemma energy_firstCut {n : ℕ} (s : ℝ) (rho : Fin (n + 1) → ℝ)
    (x : Fin (n + 2) → ℝ) :
    energy s (firstCut rho) x = (1 + s ^ 2) * x 0 ^ 2 +
      energy 0 (Fin.tail rho) (Fin.tail x) := by
  unfold energy firstCut
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, zero_mul, sub_zero, Fin.castSucc_zero, Fin.tail,
    Fin.cons_succ, Fin.castSucc_succ, Fin.succ_last, zero_pow (by decide : 2 ≠ 0), zero_add]
  ring

lemma mass_cons {n : ℕ} (β x : Fin (n + 2) → ℝ) :
    mass β x = (x 0 / β 0) ^ 2 + mass (Fin.tail β) (Fin.tail x) := by
  simp only [mass, Fin.sum_univ_succ, Fin.tail]

lemma firstCut_admissible {n : ℕ} {rho : Fin (n + 1) → ℝ} (hr : ∀ j, 0 ≤ rho j) :
    Admissible 0 rho (firstCut rho) := by
  intro j
  refine Fin.cases ?_ (fun i => ?_) j
  · exact ⟨le_rfl, hr 0⟩
  · exact ⟨hr i.succ, le_rfl⟩

lemma scalarGap_le_first_diagonal {n : ℕ} (s : ℝ) (β : Fin (n + 2) → ℝ)
    (q : Fin (n + 1) → ℝ) (hβ : ∀ i, 0 < β i) :
    scalarGap s β q ≤ (1 + s ^ 2) * β 0 ^ 2 := by
  let x : Fin (n + 2) → ℝ := Fin.cons (β 0) 0
  have hm : mass β x = 1 := by simp [mass, x, Fin.sum_univ_succ, ne_of_gt (hβ 0)]
  have he : energy s q x = (1 + s ^ 2) * β 0 ^ 2 := by
    simp [energy, x, Fin.sum_univ_succ, Fin.castSucc_succ]
    ring
  have hh := (scalarGap_spec s β q hβ).2.1 x
  simpa [hm, he] using hh

/-- With cuts allowed, just the saturated full chain and its saturated
zero-left-boundary suffix determine the exact squared gap. -/
theorem two_certificate_value {n : ℕ} (s : ℝ) (β : Fin (n + 2) → ℝ)
    (rho : Fin (n + 1) → ℝ) (hβ : ∀ i, 0 < β i) (hr : ∀ j, 0 ≤ rho j) :
    robustMinimum s β 0 rho =
      min (scalarGap s β rho) (scalarGap 0 (Fin.tail β) (Fin.tail rho)) := by
  let L := robustMinimum s β 0 rho
  let f := scalarGap s β rho
  let d := scalarGap 0 (Fin.tail β) (Fin.tail rho)
  have hf := scalarGap_spec s β rho hβ
  have hd := scalarGap_spec 0 (Fin.tail β) (Fin.tail rho) (fun i => hβ i.succ)
  have hLf : L ≤ f := robustMinimum_le_scalarGap s β 0 rho rho hβ (fun j => ⟨hr j, le_rfl⟩)
  obtain ⟨hL, hbound, q, x, hq, hx, he⟩ := robustMinimum_spec s β 0 rho hβ hr
  have hLd : L ≤ d := by
    obtain ⟨y, hy, hey⟩ := hd.2.2
    let z : Fin (n + 2) → ℝ := Fin.cons 0 y
    have hm : mass β z = 1 := by simpa [mass_cons, z] using hy
    have hen : energy s (firstCut rho) z = d := by simpa [energy_firstCut, z] using hey
    have hh := hbound (firstCut rho) (firstCut_admissible hr) z
    simpa [hm, hen] using hh
  apply le_antisymm (le_min hLf hLd)
  by_contra h
  have hlt : L < min f d := lt_of_not_ge h
  let t := (L + min f d) / 2
  have htL : L < t := by dsimp [t]; linarith
  have htf : t < f := by have := min_le_left f d; dsimp [t]; linarith
  have htd : t < d := by have := min_le_right f d; dsimp [t]; linarith
  have ht : 0 < t := lt_trans hL htL
  have hu : ∀ y, y ≠ 0 → t * mass β y < energy s rho y := by
    intro y hy
    exact lt_of_lt_of_le (mul_lt_mul_of_pos_right htf (mass_pos (fun i => ne_of_gt (hβ i)) hy)) (hf.2.1 y)
  have hc : ∀ y, y ≠ 0 → t * mass β y < energy s (firstCut rho) y := by
    intro y hy
    rw [energy_firstCut, mass_cons, mul_add]
    have hfirst : t < (1 + s ^ 2) * β 0 ^ 2 :=
      htf.trans_le (scalarGap_le_first_diagonal s β rho hβ)
    have hzero : t * (y 0 / β 0) ^ 2 ≤ (1 + s ^ 2) * y 0 ^ 2 := by
      have hh := mul_le_mul_of_nonneg_right hfirst.le (sq_nonneg (y 0 / β 0))
      have heq : ((1 + s ^ 2) * β 0 ^ 2) * (y 0 / β 0) ^ 2 = (1 + s ^ 2) * y 0 ^ 2 := by
        field_simp [ne_of_gt (hβ 0)]
      simpa [heq] using hh
    have htail := hd.2.1 (Fin.tail y)
    by_cases hyt : Fin.tail y = 0
    · have hy0 : y 0 ≠ 0 := by
        intro hz
        apply hy
        ext i
        exact Fin.cases hz (fun j => congrFun hyt j) i
      have hp : 0 < (y 0 / β 0) ^ 2 := sq_pos_of_ne_zero (div_ne_zero hy0 (ne_of_gt (hβ 0)))
      have hh := mul_lt_mul_of_pos_right hfirst hp
      have heq : ((1 + s ^ 2) * β 0 ^ 2) * (y 0 / β 0) ^ 2 = (1 + s ^ 2) * y 0 ^ 2 := by field_simp [ne_of_gt (hβ 0)]
      simpa [hyt, heq] using hh
    · have hp := mass_pos (fun i => ne_of_gt (hβ i.succ)) hyt
      have hh := mul_lt_mul_of_pos_right htd hp
      exact add_lt_add_of_le_of_lt hzero (lt_of_lt_of_le hh htail)
  have hx0 : x ≠ 0 := by intro hz; simp [hz] at hx
  have hh := energy_strict_of_two ht hβ hu hc q hq x hx0
  rw [hx, mul_one, he] at hh
  exact (not_lt_of_ge htL.le) hh

end ChiralGap
