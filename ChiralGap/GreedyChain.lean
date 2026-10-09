module

public import ChiralGap.Scalar
public import ChiralGap.EqualityPivots

@[expose] public section
noncomputable section
namespace ChiralGap

/-- Nonnegative definiteness of the literal recursive tridiagonal form. -/
def ChainNonneg {n : ℕ} (a : ℝ) (d q : Fin n → ℝ) : Prop :=
  ∀ x : Fin (n + 1) → ℝ, 0 ≤ chainForm n a d q x

lemma chainForm_headBasis (n : ℕ) (a t : ℝ) (d q : Fin n → ℝ) :
    chainForm n a d q (Fin.cons t 0) = a * t ^ 2 := by
  cases n <;> simp [chainForm]

lemma chainNonneg_first {n : ℕ} {a : ℝ} {d q : Fin n → ℝ}
    (h : ChainNonneg a d q) : 0 ≤ a := by
  have hh := h (Fin.cons 1 0)
  simpa [chainForm_headBasis] using hh

lemma chainNonneg_first_pos {n : ℕ} {a : ℝ} {d q : Fin (n + 1) → ℝ}
    (h : ChainNonneg a d q) (hq : 0 < q 0) : 0 < a := by
  have ha := chainNonneg_first h
  by_contra hn
  have haz : a = 0 := le_antisymm (le_of_not_gt hn) ha
  let t := (d 0 + q 0 ^ 2 + 1) / (2 * q 0)
  have hh := h (Fin.cons t (Fin.cons 1 0))
  have hqne : q 0 ≠ 0 := ne_of_gt hq
  simp only [chainForm, haz, Fin.cons_zero, Fin.cons_one,
    zero_mul, zero_sub, Fin.tail_cons, chainForm_headBasis, one_pow, mul_one] at hh
  dsimp [t] at hh
  field_simp [hqne] at hh
  nlinarith

lemma chainNonneg_schur {n : ℕ} {a : ℝ} {d q : Fin (n + 1) → ℝ}
    (ha : 0 < a) :
    ChainNonneg a d q ↔
      ChainNonneg (pivotStep (d 0) a (q 0)) (Fin.tail d) (Fin.tail q) := by
  constructor
  · intro h y
    have hh := h (Fin.cons (q 0 / a * y 0) y)
    rw [chainForm_complete (ne_of_gt ha)] at hh
    simpa [pivotStep, Fin.tail] using hh
  · intro h x
    rw [chainForm_complete (ne_of_gt ha)]
    exact add_nonneg (mul_nonneg ha.le (sq_nonneg _)) (h _)

lemma greedy_update_le {a ell rho q d : ℝ} (ha : 0 < a)
    (hl : 0 ≤ ell) (hq : ell ≤ q ∧ q ≤ rho) :
    pivotStep d a (greedyEndpoint ell rho a) ≤ pivotStep d a q := by
  have hh := endpointMismatch_nonneg hl ha hq.1 hq.2
  unfold pivotStep
  nlinarith

/-- A positive-link box which is nonnegative definite and has a null vector
admits the complete greedy pivot certificate. No nonsingularity is assumed. -/
theorem exists_greedy_pivots (n : ℕ) {a : ℝ} {d ell rho : Fin n → ℝ}
    (hl : ∀ j, 0 < ell j) (horder : ∀ j, ell j ≤ rho j)
    (hN : ∀ q, Admissible ell rho q → ChainNonneg a d q)
    (hZ : ∃ q x, Admissible ell rho q ∧ x ≠ 0 ∧ chainForm n a d q x = 0) :
    ∃ p : Fin (n + 1) → ℝ,
      p 0 = a ∧
      (∀ j : Fin n, p j.succ = pivotStep (d j) (p j.castSucc)
        (greedyEndpoint (ell j) (rho j) (p j.castSucc))) ∧
      (∀ j : Fin n, 0 < p j.castSucc) ∧ p (Fin.last n) = 0 := by
  induction n generalizing a with
  | zero =>
      rcases hZ with ⟨q, x, hq, hx, hz⟩
      have hx0 : x 0 ≠ 0 := by
        intro hh
        apply hx
        ext i
        have hi : i = 0 := Fin.eq_zero i
        simpa [hi] using hh
      have ha : a = 0 := (mul_eq_zero.mp hz).resolve_right (pow_ne_zero 2 hx0)
      refine ⟨fun _ => 0, ha.symm, ?_, ?_, rfl⟩
      · intro j; exact Fin.elim0 j
      · intro j; exact Fin.elim0 j
  | succ n ih =>
      have hell : Admissible ell rho ell := fun j => ⟨le_rfl, horder j⟩
      have ha := chainNonneg_first_pos (hN ell hell) (hl 0)
      let g := greedyEndpoint (ell 0) (rho 0) a
      let b := pivotStep (d 0) a g
      have hg : ell 0 ≤ g ∧ g ≤ rho 0 := greedyEndpoint_mem (horder 0)
      have hNt : ∀ r, Admissible (Fin.tail ell) (Fin.tail rho) r →
          ChainNonneg b (Fin.tail d) r := by
        intro r hr
        have hadm : Admissible ell rho (Fin.cons g r) := by
          intro j
          refine Fin.cases hg (fun k => hr k) j
        have hh := (chainNonneg_schur ha).1 (hN (Fin.cons g r) hadm)
        simpa [b] using hh
      rcases hZ with ⟨q, x, hq, hx, hz⟩
      have hqt : Admissible (Fin.tail ell) (Fin.tail rho) (Fin.tail q) :=
        fun j => hq j.succ
      have hxt : Fin.tail x ≠ 0 := by
        intro ht
        have hx1 : x 1 = 0 := congrFun ht 0
        rw [chainForm_complete (ne_of_gt ha), ht, hx1, chainForm_zero] at hz
        have hx0 : x 0 = 0 := by
          simp only [mul_zero, sub_zero, add_zero] at hz
          exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hz).resolve_left (ne_of_gt ha))
        apply hx
        ext j
        refine Fin.cases hx0 (fun k => congrFun ht k) j
      have hbt : b ≤ pivotStep (d 0) a (q 0) :=
        greedy_update_le ha (hl 0).le (hq 0)
      have hz' : chainForm n b (Fin.tail d) (Fin.tail q) (Fin.tail x) = 0 := by
        have hn := hNt (Fin.tail q) hqt (Fin.tail x)
        rw [chainForm_complete (ne_of_gt ha)] at hz
        change a * (x 0 - q 0 / a * x 1) ^ 2 +
          chainForm n (pivotStep (d 0) a (q 0)) (Fin.tail d) (Fin.tail q) (Fin.tail x) = 0 at hz
        rw [chainForm_head n b] at hz
        have hs := mul_nonneg ha.le (sq_nonneg (x 0 - q 0 / a * x 1))
        have hm := mul_nonneg (sub_nonneg.mpr hbt) (sq_nonneg ((Fin.tail x) 0))
        linarith
      rcases ih (fun j => hl j.succ) (fun j => horder j.succ) hNt
        ⟨Fin.tail q, Fin.tail x, hqt, hxt, hz'⟩ with ⟨p, hp0, hpstep, hppos, hplast⟩
      refine ⟨Fin.cons a p, rfl, ?_, ?_, ?_⟩
      · intro j
        refine Fin.cases ?_ (fun k => ?_) j
        · simpa [b, g] using hp0
        · simpa [Fin.castSucc_succ, Fin.tail] using hpstep k
      · intro j
        refine Fin.cases ?_ (fun k => ?_) j
        · simpa using ha
        · simpa [Fin.castSucc_succ] using hppos k
      · simpa using hplast

end ChiralGap
