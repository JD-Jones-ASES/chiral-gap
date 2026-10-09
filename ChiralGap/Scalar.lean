module

public import ChiralGap.Basic

public section
noncomputable section
namespace ChiralGap

/-- Recursive tridiagonal quadratic form; the diagonal after the first site is
`d j + q j ^ 2`, with adjacent entry `-q j`. -/
@[expose] def chainForm : (n : ℕ) → ℝ → (Fin n → ℝ) → (Fin n → ℝ) →
    (Fin (n + 1) → ℝ) → ℝ
  | 0, a, _, _, x => a * x 0 ^ 2
  | n + 1, a, d, q, x => a * x 0 ^ 2 - 2 * q 0 * x 0 * x 1 +
      chainForm n (d 0 + q 0 ^ 2) (Fin.tail d) (Fin.tail q) (Fin.tail x)

/-- Strict positive definiteness of the recursive form. -/
@[expose] def ChainPositive {n : ℕ} (a : ℝ) (d q : Fin n → ℝ) : Prop :=
  ∀ x : Fin (n + 1) → ℝ, x ≠ 0 → 0 < chainForm n a d q x

@[simp] lemma chainForm_zero (n : ℕ) (a : ℝ) (d q : Fin n → ℝ) :
    chainForm n a d q 0 = 0 := by
  induction n generalizing a with
  | zero => simp [chainForm]
  | succ n ih =>
      simp only [chainForm, Pi.zero_apply, zero_pow (by decide : 2 ≠ 0), mul_zero, sub_self, zero_add]
      exact ih _ _ _

lemma chainForm_head (n : ℕ) (a b : ℝ) (d q : Fin n → ℝ)
    (x : Fin (n + 1) → ℝ) :
    chainForm n b d q x = chainForm n a d q x + (b - a) * x 0 ^ 2 := by
  cases n <;> simp only [chainForm] <;> ring

lemma chainPositive_mono {n : ℕ} {a b : ℝ} {d q : Fin n → ℝ}
    (hab : a ≤ b) (h : ChainPositive a d q) : ChainPositive b d q := by
  intro x hx
  rw [chainForm_head n a b]
  have hnonneg : 0 ≤ (b - a) * x 0 ^ 2 := mul_nonneg (sub_nonneg.mpr hab) (sq_nonneg _)
  exact add_pos_of_pos_of_nonneg (h x hx) hnonneg

lemma chainForm_complete {n : ℕ} {a : ℝ} (ha : a ≠ 0)
    (d q : Fin (n + 1) → ℝ) (x : Fin (n + 2) → ℝ) :
    chainForm (n + 1) a d q x =
      a * (x 0 - q 0 / a * x 1) ^ 2 +
      chainForm n (d 0 + q 0 ^ 2 * (1 - 1 / a))
        (Fin.tail d) (Fin.tail q) (Fin.tail x) := by
  rw [chainForm, chainForm_head n (d 0 + q 0 ^ 2 * (1 - 1 / a))]
  simp only [Fin.tail, Fin.succ_zero_eq_one]
  field_simp
  ring

lemma chainPositive_first {n : ℕ} {a : ℝ} {d q : Fin n → ℝ}
    (h : ChainPositive a d q) : 0 < a := by
  let x : Fin (n + 1) → ℝ := Fin.cons 1 0
  have hx : x ≠ 0 := by intro hh; have := congrFun hh 0; simp [x] at this
  have hh := h x hx
  cases n with
  | zero => simpa [chainForm, x] using hh
  | succ n => simpa [chainForm, x, Fin.tail] using hh

lemma chainPositive_schur {n : ℕ} {a : ℝ} {d q : Fin (n + 1) → ℝ}
    (ha : 0 < a) :
    ChainPositive a d q ↔
      ChainPositive (d 0 + q 0 ^ 2 * (1 - 1 / a)) (Fin.tail d) (Fin.tail q) := by
  constructor
  · intro h y hy
    let x : Fin (n + 2) → ℝ := Fin.cons (q 0 / a * y 0) y
    have hx : x ≠ 0 := by
      intro hh
      apply hy
      funext i
      exact congrFun hh i.succ
    have hh := h x hx
    rw [chainForm_complete (ne_of_gt ha)] at hh
    simpa [x, Fin.tail] using hh
  · intro h x hx
    rw [chainForm_complete (ne_of_gt ha)]
    by_cases ht : Fin.tail x = 0
    · have hx0 : x 0 ≠ 0 := by
        intro hz
        apply hx
        ext i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact hz
        · exact congrFun ht j
      have hx1 : x 1 = 0 := congrFun ht 0
      rw [ht, chainForm_zero, hx1]
      simpa using mul_pos ha (sq_pos_of_ne_zero hx0)
    · exact add_pos_of_nonneg_of_pos (mul_nonneg ha.le (sq_nonneg _)) (h _ ht)

lemma chainPositive_zero_iff (a : ℝ) (d q : Fin 0 → ℝ) :
    ChainPositive a d q ↔ 0 < a := by
  constructor
  · exact chainPositive_first
  · intro ha x hx
    have hx0 : x 0 ≠ 0 := by
      intro hz
      apply hx
      ext i
      have : i = 0 := Fin.eq_zero i
      simpa [this] using hz
    exact mul_pos ha (sq_pos_of_ne_zero hx0)

lemma update_lower {a ell q : ℝ} (ha : 0 < a) (ha1 : 1 ≤ a)
    (hl : 0 ≤ ell) (hlq : ell ≤ q) :
    ell ^ 2 * (1 - 1 / a) ≤ q ^ 2 * (1 - 1 / a) := by
  have hsq : ell ^ 2 ≤ q ^ 2 := by nlinarith
  have hc : 0 ≤ 1 - 1 / a := by
    have : 1 / a ≤ 1 := (div_le_iff₀ ha).2 (by nlinarith)
    linarith
  exact mul_le_mul_of_nonneg_right hsq hc

lemma update_upper {a q rho : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hq : 0 ≤ q) (hqr : q ≤ rho) :
    rho ^ 2 * (1 - 1 / a) ≤ q ^ 2 * (1 - 1 / a) := by
  have hsq : q ^ 2 ≤ rho ^ 2 := by nlinarith
  have hc : 1 - 1 / a ≤ 0 := by
    have : 1 ≤ 1 / a := (le_div_iff₀ ha).2 (by nlinarith)
    linarith
  exact mul_le_mul_of_nonpos_right hsq hc

lemma update_lt_one {a d q : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hd : d < 1) : d + q ^ 2 * (1 - 1 / a) < 1 := by
  have hc : 1 - 1 / a ≤ 0 := by
    have : 1 ≤ 1 / a := (le_div_iff₀ ha).2 (by nlinarith)
    linarith
  have hm := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg q) hc
  linarith

/-- Below the pivot threshold one, the fully upper endpoint controls the box. -/
lemma chainPositive_of_upper (n : ℕ) {a : ℝ} {d ell rho : Fin n → ℝ}
    (ha1 : a < 1) (hd : ∀ j, d j < 1) (hl : ∀ j, 0 ≤ ell j)
    (hu : ChainPositive a d rho) :
    ∀ q, Admissible ell rho q → ChainPositive a d q := by
  induction n generalizing a with
  | zero =>
      intro q hq
      exact (chainPositive_zero_iff _ _ _).2 (chainPositive_first hu)
  | succ n ih =>
      intro q hq
      have ha := chainPositive_first hu
      apply (chainPositive_schur ha).2
      have ht := (chainPositive_schur ha).1 hu
      have hsmall := update_lt_one ha ha1.le (hd 0) (q := rho 0)
      have htail : ChainPositive (d 0 + rho 0 ^ 2 * (1 - 1 / a))
          (Fin.tail d) (Fin.tail q) :=
        ih hsmall (fun j => hd j.succ) (fun j => hl j.succ) ht
          (Fin.tail q) (fun j => hq j.succ)
      apply chainPositive_mono (h := htail)
      linarith [update_upper ha ha1.le
        (le_trans (hl 0) (hq 0).1) (hq 0).2]

@[simp] lemma candidate_zero {n : ℕ} (ell rho : Fin n → ℝ) :
    candidate ell rho (0 : Fin (n + 1)) = rho := by
  ext j
  simp [candidate]

@[simp] lemma candidate_succ_zero {n : ℕ} (ell rho : Fin (n + 1) → ℝ)
    (k : Fin (n + 1)) : candidate ell rho k.succ 0 = ell 0 := by
  simp [candidate]

@[simp] lemma candidate_tail {n : ℕ} (ell rho : Fin (n + 1) → ℝ)
    (k : Fin (n + 1)) :
    Fin.tail (candidate ell rho k.succ) = candidate (Fin.tail ell) (Fin.tail rho) k := by
  ext j
  simp [candidate, Fin.tail]

/-- The one-switch positivity theorem, valid also when lower endpoints vanish.
There are `n + 1` candidates for `n + 1` sites. -/
theorem chainPositive_of_candidates (n : ℕ) {a : ℝ} {d ell rho : Fin n → ℝ}
    (hd : ∀ j, d j < 1) (hl : ∀ j, 0 ≤ ell j)
    (hc : ∀ k, ChainPositive a d (candidate ell rho k)) :
    ∀ q, Admissible ell rho q → ChainPositive a d q := by
  induction n generalizing a with
  | zero =>
      intro q hq
      exact (chainPositive_zero_iff _ _ _).2 (chainPositive_first (hc 0))
  | succ n ih =>
      intro q hq
      have hu : ChainPositive a d rho := by simpa using hc 0
      have ha := chainPositive_first hu
      by_cases ha1 : a < 1
      · exact chainPositive_of_upper (n + 1) ha1 hd hl hu q hq
      · have ha1' : 1 ≤ a := le_of_not_gt ha1
        apply (chainPositive_schur ha).2
        have hc' : ∀ k : Fin (n + 1),
            ChainPositive (d 0 + ell 0 ^ 2 * (1 - 1 / a))
              (Fin.tail d) (candidate (Fin.tail ell) (Fin.tail rho) k) := by
          intro k
          have hh := (chainPositive_schur ha).1 (hc k.succ)
          simpa using hh
        have htail := ih (fun j => hd j.succ) (fun j => hl j.succ) hc'
          (Fin.tail q) (fun j => hq j.succ)
        apply chainPositive_mono (h := htail)
        linarith [update_lower ha ha1' (hl 0) (hq 0).1]

lemma chainForm_sum (n : ℕ) (a : ℝ) (d q : Fin n → ℝ)
    (x : Fin (n + 1) → ℝ) :
    chainForm n a d q x = a * x 0 ^ 2 +
      ∑ j, ((d j + q j ^ 2) * x j.succ ^ 2 -
        2 * q j * x j.castSucc * x j.succ) := by
  induction n generalizing a with
  | zero => simp [chainForm]
  | succ n ih =>
      rw [chainForm, ih, Fin.sum_univ_succ]
      simp only [Fin.tail, Fin.succ_zero_eq_one, Fin.castSucc_zero, Fin.castSucc_succ]
      ring

/-- The recursive form is exactly the weighted chain energy shifted by `L`. -/
theorem chainForm_eq_energy_sub_mass {n : ℕ} (s L : ℝ)
    (β : Fin (n + 1) → ℝ) (q : Fin n → ℝ) (x : Fin (n + 1) → ℝ) :
    chainForm n (1 + s ^ 2 - L / β 0 ^ 2)
      (fun j => 1 - L / β j.succ ^ 2) q x = energy s q x - L * mass β x := by
  rw [chainForm_sum]
  have hsum : (∑ j : Fin n, x j.castSucc ^ 2) + x (Fin.last n) ^ 2 =
      x 0 ^ 2 + ∑ j : Fin n, x j.succ ^ 2 := by
    have h₁ := Fin.sum_univ_castSucc (fun i : Fin (n + 1) => x i ^ 2)
    have h₂ := Fin.sum_univ_succ (fun i : Fin (n + 1) => x i ^ 2)
    linarith
  unfold energy mass
  rw [Fin.sum_univ_succ, mul_add]
  simp_rw [Finset.mul_sum, div_pow]
  have hterm : ∀ j : Fin n,
      (1 - L / β j.succ ^ 2 + q j ^ 2) * x j.succ ^ 2 -
          2 * q j * x j.castSucc * x j.succ =
      (x j.castSucc - q j * x j.succ) ^ 2 - L * (x j.succ ^ 2 / β j.succ ^ 2) +
          x j.succ ^ 2 - x j.castSucc ^ 2 := by intro j; ring
  simp_rw [hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp only [Finset.sum_sub_distrib]
  linear_combination -hsum

/-- Testing strict positivity on the one-switch candidates suffices for the
literal shifted chain energy, with zero lower endpoints permitted. -/
theorem energy_strict_of_candidates {n : ℕ} {s L : ℝ}
    {β : Fin (n + 1) → ℝ} {ell rho : Fin n → ℝ}
    (hL : 0 < L) (hβ : ∀ i, 0 < β i) (hl : ∀ j, 0 ≤ ell j)
    (hc : ∀ k : Fin (n + 1), ∀ x : Fin (n + 1) → ℝ, x ≠ 0 →
      L * mass β x < energy s (candidate ell rho k) x) :
    ∀ q, Admissible ell rho q → ∀ x : Fin (n + 1) → ℝ, x ≠ 0 →
      L * mass β x < energy s q x := by
  have hd : ∀ j : Fin n, 1 - L / β j.succ ^ 2 < 1 := by
    intro j
    have hp : 0 < L / β j.succ ^ 2 := div_pos hL (sq_pos_of_pos (hβ _))
    linarith
  have hh := chainPositive_of_candidates n (a := 1 + s ^ 2 - L / β 0 ^ 2) hd hl
    (fun k x hx => by
      rw [chainForm_eq_energy_sub_mass]
      exact sub_pos.mpr (hc k x hx))
  intro q hq x hx
  have hh' := hh q hq x hx
  rw [chainForm_eq_energy_sub_mass] at hh'
  exact sub_pos.mp hh'

end ChiralGap
