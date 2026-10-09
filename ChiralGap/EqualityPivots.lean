module

public import Mathlib

@[expose] public section

noncomputable section

namespace ChiralGap

/-- The normalized Schur-complement update. -/
def pivotStep (d a q : ℝ) : ℝ := d + q ^ 2 * (1 - 1 / a)

/-- The endpoint chosen by the sign of a preceding positive pivot. -/
def greedyEndpoint (ell rho a : ℝ) : ℝ := if 1 ≤ a then ell else rho

/-- Membership in the full minimizing face, including a free coordinate at a tie. -/
def EndpointRule (ell rho a q : ℝ) : Prop :=
  (1 < a → q = ell) ∧ (a < 1 → q = rho)

theorem greedyEndpoint_mem {ell rho a : ℝ} (h : ell ≤ rho) :
    ell ≤ greedyEndpoint ell rho a ∧ greedyEndpoint ell rho a ≤ rho := by
  unfold greedyEndpoint
  split_ifs <;> constructor <;> linarith

theorem pivotStep_strictMono {d a b q : ℝ} (ha : 0 < a) (hab : a < b)
    (hq : 0 < q) : pivotStep d a q < pivotStep d b q := by
  have hi := one_div_lt_one_div_of_lt ha hab
  have hq2 : 0 < q ^ 2 := sq_pos_of_pos hq
  unfold pivotStep
  nlinarith

theorem pivotStep_mono {d a b q : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    pivotStep d a q ≤ pivotStep d b q := by
  have hi := one_div_le_one_div_of_le ha hab
  have hq2 : 0 ≤ q ^ 2 := sq_nonneg q
  unfold pivotStep
  nlinarith

/-- Every endpoint mismatch in the fixed-pivot square decomposition is nonnegative. -/
theorem endpointMismatch_nonneg {ell rho a q : ℝ} (hell : 0 ≤ ell)
    (ha : 0 < a) (hql : ell ≤ q) (hqr : q ≤ rho) :
    0 ≤ (q ^ 2 - (greedyEndpoint ell rho a) ^ 2) * (1 - 1 / a) := by
  have hq : 0 ≤ q := le_trans hell hql
  have hr : 0 ≤ rho := le_trans hq hqr
  unfold greedyEndpoint
  split_ifs with h
  · have hi : 1 / a ≤ 1 := (div_le_one ha).2 h
    have hs : ell ^ 2 ≤ q ^ 2 := sq_le_sq₀ hell hq |>.2 hql
    exact mul_nonneg (sub_nonneg.2 hs) (sub_nonneg.2 hi)
  · have hi : 1 ≤ 1 / a := (le_div_iff₀ ha).2 (by linarith)
    have hs : q ^ 2 ≤ rho ^ 2 := sq_le_sq₀ hq hr |>.2 hqr
    exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.2 hs) (sub_nonpos.2 hi)

/-- With positive lower bounds, equality in the endpoint comparison is exact. -/
theorem endpointMismatch_eq_zero_iff {ell rho a q : ℝ} (hell : 0 < ell)
    (ha : 0 < a) (hql : ell ≤ q) (hqr : q ≤ rho) :
    (q ^ 2 - (greedyEndpoint ell rho a) ^ 2) * (1 - 1 / a) = 0 ↔
      EndpointRule ell rho a q := by
  have hq : 0 < q := lt_of_lt_of_le hell hql
  have hr : 0 < rho := lt_of_lt_of_le hq hqr
  rcases lt_trichotomy a 1 with hlt | heq | hgt
  · have hg : greedyEndpoint ell rho a = rho := by simp [greedyEndpoint, not_le.mpr hlt]
    have hc : 1 - 1 / a ≠ 0 := by
      have hi : 1 < 1 / a := (lt_div_iff₀ ha).2 (by linarith)
      linarith
    simp only [hg, mul_eq_zero, hc, or_false, EndpointRule]
    constructor
    · intro h
      have he : q = rho := by nlinarith
      exact ⟨by intro h; linarith, by intro _; exact he⟩
    · intro h
      rw [h.2 hlt]
      ring
  · subst a
    simp [EndpointRule]
  · have hg : greedyEndpoint ell rho a = ell := by simp [greedyEndpoint, le_of_lt hgt]
    have hc : 1 - 1 / a ≠ 0 := by
      have hi : 1 / a < 1 := (div_lt_one ha).2 hgt
      linarith
    simp only [hg, mul_eq_zero, hc, or_false, EndpointRule]
    constructor
    · intro h
      have he : q = ell := by nlinarith
      exact ⟨by intro _; exact he, by intro h; linarith⟩
    · intro h
      rw [h.1 hgt]
      ring

theorem pivotStep_lt_one {d a q : ℝ} (hd : d < 1) (ha : 0 < a)
    (ha1 : a ≤ 1) : pivotStep d a q < 1 := by
  have hi : 1 ≤ 1 / a := (le_div_iff₀ ha).2 (by linarith)
  have hs := sq_nonneg q
  unfold pivotStep
  nlinarith

/-- Once a positive pivot is at most one, every later proper pivot is strictly below one. -/
theorem pivot_lt_one_of_le {n : ℕ} {a d q : ℕ → ℝ}
    (hpos : ∀ i < n, 0 < a i) (hd : ∀ i < n, d i < 1)
    (hrec : ∀ i < n, a (i + 1) = pivotStep (d i) (a i) (q i))
    {i j : ℕ} (hij : i < j) (hjn : j ≤ n) (hi : a i ≤ 1) : a j < 1 := by
  induction j with
  | zero => omega
  | succ j ih =>
    have hjn : j < n := by omega
    rw [hrec j hjn]
    apply pivotStep_lt_one (hd j hjn) (hpos j hjn)
    rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hij) with he | he
    · simpa [← he] using hi
    · exact le_of_lt (ih he (by omega))

/-- In a positive-pivot chain with positive spectral parameter there is at most one tie. -/
theorem pivot_tie_unique {n : ℕ} {a d q : ℕ → ℝ}
    (hpos : ∀ i < n, 0 < a i) (hd : ∀ i < n, d i < 1)
    (hrec : ∀ i < n, a (i + 1) = pivotStep (d i) (a i) (q i))
    {i j : ℕ} (hin : i ≤ n) (hjn : j ≤ n) (hi : a i = 1) (hj : a j = 1) :
    i = j := by
  rcases lt_trichotomy i j with h | h | h
  · have hh := pivot_lt_one_of_le hpos hd hrec h hjn (le_of_eq hi)
    linarith
  · exact h
  · have hh := pivot_lt_one_of_le hpos hd hrec h hin (le_of_eq hj)
    linarith

end ChiralGap
