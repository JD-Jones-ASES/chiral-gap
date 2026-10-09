module

public import Mathlib

public section

noncomputable section

namespace ChiralGap

/-- A named first site keeps dependent-index proofs identical across the independent statement. -/
abbrev firstSite (n : ℕ) : Fin (n + 1) := ⟨0, Nat.zero_lt_succ n⟩

@[simp] theorem firstSite_eq_zero (n : ℕ) : firstSite n = 0 := rfl

/-- A chain with `n` edges has `n + 1` scalar sites. -/
@[expose] def energy {n : ℕ} (s : ℝ) (q : Fin n → ℝ) (x : Fin (n + 1) → ℝ) : ℝ :=
  s ^ 2 * x 0 ^ 2 + ∑ j, (x j.castSucc - q j * x j.succ) ^ 2 +
    x (Fin.last n) ^ 2

/-- The strong-bond weighted square norm. -/
@[expose] def mass {n : ℕ} (β x : Fin (n + 1) → ℝ) : ℝ :=
  ∑ i, (x i / β i) ^ 2

/-- Membership of the closed box of ratio magnitudes. -/
@[expose] def Admissible {n : ℕ} (ell rho q : Fin n → ℝ) : Prop :=
  ∀ j, ell j ≤ q j ∧ q j ≤ rho j

/-- The `n + 1` endpoint configurations, with one change from lower to upper. -/
@[expose] def candidate {n : ℕ} (ell rho : Fin n → ℝ) (k : Fin (n + 1)) : Fin n → ℝ :=
  fun j => if j.val < k.val then ell j else rho j

/-- The weighted Rayleigh quotient of the literal open-chain residual energy. -/
@[expose] def rayleigh {n : ℕ} (s : ℝ) (β : Fin (n + 1) → ℝ)
    (q : Fin n → ℝ) (x : Fin (n + 1) → ℝ) : ℝ :=
  energy s q x / mass β x

/-- A uniform scalar lower bound, without positivity assumptions folded into it. -/
@[expose] def ScalarLowerBound {n : ℕ} (s : ℝ) (β : Fin (n + 1) → ℝ)
    (ell rho : Fin n → ℝ) (L : ℝ) : Prop :=
  ∀ q, Admissible ell rho q → ∀ x, L * mass β x ≤ energy s q x

lemma candidate_admissible {n : ℕ} {ell rho : Fin n → ℝ}
    (h : ∀ j, ell j ≤ rho j) (k : Fin (n + 1)) :
    Admissible ell rho (candidate ell rho k) := by
  intro j
  simp only [candidate]
  split_ifs <;> exact ⟨by first | exact le_rfl | exact h j,
    by first | exact le_rfl | exact h j⟩

lemma energy_nonneg {n : ℕ} (s : ℝ) (q : Fin n → ℝ)
    (x : Fin (n + 1) → ℝ) : 0 ≤ energy s q x := by
  unfold energy
  positivity

lemma mass_nonneg {n : ℕ} (β x : Fin (n + 1) → ℝ) : 0 ≤ mass β x := by
  unfold mass
  positivity

@[simp] lemma energy_zero {n : ℕ} (s : ℝ) (q : Fin n → ℝ) :
    energy s q (0 : Fin (n + 1) → ℝ) = 0 := by simp [energy]

@[simp] lemma mass_zero {n : ℕ} (β : Fin (n + 1) → ℝ) :
    mass β (0 : Fin (n + 1) → ℝ) = 0 := by simp [mass]

end ChiralGap
