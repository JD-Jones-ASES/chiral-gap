module

public import ChiralGap.Value

@[expose] public section
noncomputable section
namespace ChiralGap
open scoped Matrix

/-- The boundary row, the open-chain interior rows, and the last boundary row. -/
abbrev ResidualRow (n : ℕ) := Unit ⊕ (Fin n ⊕ Unit)

/-- The literal rectangular residual matrix `Q(q) D(β)`. -/
def residualMatrix {n : ℕ} (s : ℝ) (β : Fin (n + 1) → ℝ) (q : Fin n → ℝ) :
    Matrix (ResidualRow n) (Fin (n + 1)) ℝ := fun r =>
  match r with
  | .inl _ => Pi.single (firstSite n) (s * β (firstSite n))
  | .inr (.inl j) =>
      Pi.single j.castSucc (β j.castSucc) - Pi.single j.succ (q j * β j.succ)
  | .inr (.inr _) => Pi.single (Fin.last n) (β (Fin.last n))

/-- The actual symmetric Gram matrix of the scalar chain. -/
def gram {n : ℕ} (s : ℝ) (β : Fin (n + 1) → ℝ) (q : Fin n → ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  (residualMatrix s β q).transpose * residualMatrix s β q

lemma residualMatrix_mulVec {n : ℕ} (s : ℝ) (β y : Fin (n + 1) → ℝ)
    (q : Fin n → ℝ) :
    residualMatrix s β q *ᵥ y =
      Sum.elim (fun _ => s * (β 0 * y 0))
        (Sum.elim (fun j => β j.castSucc * y j.castSucc - q j * (β j.succ * y j.succ))
          (fun _ => β (Fin.last n) * y (Fin.last n))) := by
  funext i
  rcases i with u | j | u
  · simp only [Matrix.mulVec, residualMatrix, single_dotProduct, Sum.elim_inl, firstSite_eq_zero]
    ring
  · simp only [Matrix.mulVec, residualMatrix, sub_dotProduct, single_dotProduct,
      Sum.elim_inr, Sum.elim_inl]
    ring
  · simp [Matrix.mulVec, residualMatrix]

/-- The Gram quadratic form is exactly the scalar energy after the diagonal change of variables. -/
theorem gram_quadratic {n : ℕ} (s : ℝ) (β : Fin (n + 1) → ℝ)
    (q : Fin n → ℝ) (y : Fin (n + 1) → ℝ) :
    y ⬝ᵥ (gram s β q *ᵥ y) = energy s q (fun i => β i * y i) := by
  rw [gram, ← Matrix.mulVec_mulVec, Matrix.dotProduct_transpose_mulVec]
  rw [residualMatrix_mulVec]
  simp only [dotProduct, Fintype.sum_sum_type, Fintype.sum_unique, Sum.elim_inl,
    Sum.elim_inr, energy]
  simp_rw [← sq]
  ring

/-- Every scalar chain Gram matrix is positive definite for positive strong bonds,
regardless of the signs of the real ratios. -/
theorem gram_posDef {n : ℕ} (s : ℝ) (β : Fin (n + 1) → ℝ)
    (q : Fin n → ℝ) (hβ : ∀ i, 0 < β i) : (gram s β q).PosDef := by
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  refine ⟨?_, ?_⟩
  · have hh := Matrix.isHermitian_conjTranspose_mul_self (residualMatrix s β q)
    simpa only [gram, Matrix.conjTranspose_eq_transpose_of_trivial] using hh
  · intro y hy
    have hstar : star y = y := by ext i; simp
    rw [hstar, gram_quadratic]
    apply energy_pos
    intro hz
    apply hy
    ext i
    have hh := congrFun hz i
    exact (mul_eq_zero.mp hh).resolve_left (ne_of_gt (hβ i))

/-- The fixed-chain variational gap is the attained least Rayleigh value of the
actual Gram matrix, so it can be used without choosing an eigenvalue ordering. -/
theorem scalarGap_gram_spec {n : ℕ} (s : ℝ) (β : Fin (n + 1) → ℝ)
    (q : Fin n → ℝ) (hβ : ∀ i, 0 < β i) :
    (∀ y, scalarGap s β q * (∑ i, y i ^ 2) ≤ y ⬝ᵥ (gram s β q *ᵥ y)) ∧
      ∃ y, (∑ i, y i ^ 2) = 1 ∧ y ⬝ᵥ (gram s β q *ᵥ y) = scalarGap s β q := by
  obtain ⟨_, hbound, x, hx, he⟩ := scalarGap_spec s β q hβ
  constructor
  · intro y
    rw [gram_quadratic]
    have hh := hbound (fun i => β i * y i)
    have hm : mass β (fun i => β i * y i) = ∑ i, y i ^ 2 := by
      unfold mass
      apply Finset.sum_congr rfl
      intro i _
      simp [ne_of_gt (hβ i)]
    simpa only [hm] using hh
  · refine ⟨fun i => x i / β i, hx, ?_⟩
    rw [gram_quadratic]
    have hv : (fun i => β i * (x i / β i)) = x := by
      ext i
      field_simp [ne_of_gt (hβ i)]
    rw [hv, he]

lemma dotProduct_shift {m : ℕ} (M : Matrix (Fin m) (Fin m) ℝ) (L : ℝ)
    (y : Fin m → ℝ) :
    y ⬝ᵥ ((M - Matrix.diagonal (fun _ => L)) *ᵥ y) =
      y ⬝ᵥ (M *ᵥ y) - L * ∑ i, y i ^ 2 := by
  rw [Matrix.sub_mulVec, dotProduct_sub]
  congr 1
  simp only [dotProduct, Matrix.mulVec_diagonal, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The fixed-chain gap is an actual eigenvalue, attained by a unit eigenvector. -/
theorem scalarGap_eigenvector {n : ℕ} (s : ℝ) (β : Fin (n + 1) → ℝ)
    (q : Fin n → ℝ) (hβ : ∀ i, 0 < β i) :
    ∃ y : Fin (n + 1) → ℝ, (∑ i, y i ^ 2) = 1 ∧
      gram s β q *ᵥ y = scalarGap s β q • y := by
  obtain ⟨hb, y, hy, he⟩ := scalarGap_gram_spec s β q hβ
  let A := gram s β q - Matrix.diagonal (fun _ => scalarGap s β q)
  have hA : A.PosSemidef := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · exact (gram_posDef s β q hβ).isHermitian.sub (Matrix.isHermitian_diagonal _)
    · intro z
      have hs : star z = z := by ext i; simp
      rw [hs]
      change 0 ≤ z ⬝ᵥ ((gram s β q - Matrix.diagonal (fun _ => scalarGap s β q)) *ᵥ z)
      rw [dotProduct_shift]
      exact sub_nonneg.mpr (hb z)
  have hz : A *ᵥ y = 0 := by
    apply hA.dotProduct_mulVec_zero_iff.mp
    have hs : star y = y := by ext i; simp
    rw [hs]
    change y ⬝ᵥ ((gram s β q - Matrix.diagonal (fun _ => scalarGap s β q)) *ᵥ y) = 0
    rw [dotProduct_shift, hy, he]
    ring
  refine ⟨y, hy, ?_⟩
  have hh : gram s β q *ᵥ y - Matrix.diagonal (fun _ => scalarGap s β q) *ᵥ y = 0 :=
    by simpa [A, Matrix.sub_mulVec] using hz
  have hh' := sub_eq_zero.mp hh
  simpa [Matrix.mulVec_diagonal, Pi.smul_apply] using hh'

/-- No real eigenvalue of the actual Gram matrix lies below `scalarGap`. -/
theorem scalarGap_le_eigenvalue {n : ℕ} (s : ℝ) (β : Fin (n + 1) → ℝ)
    (q : Fin n → ℝ) (hβ : ∀ i, 0 < β i) (t : ℝ)
    {y : Fin (n + 1) → ℝ} (hy : y ≠ 0) (he : gram s β q *ᵥ y = t • y) :
    scalarGap s β q ≤ t := by
  have hb := (scalarGap_gram_spec s β q hβ).1 y
  have hm : 0 < ∑ i, y i ^ 2 := by
    have hh := mass_pos (β := fun _ => 1) (fun _ => one_ne_zero) hy
    simpa [mass] using hh
  rw [he] at hb
  have hd : y ⬝ᵥ (t • y) = t * ∑ i, y i ^ 2 := by
    simp only [dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hd] at hb
  exact (mul_le_mul_iff_left₀ hm).mp hb

end ChiralGap
