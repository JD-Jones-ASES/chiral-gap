module

public import ChiralGap.Basic
public import ChiralGap.EqualityPivots

@[expose] public section

noncomputable section

namespace ChiralGap

/-- A finite, explicit positive-pivot certificate at the optimal value.
Its endpoint recursion is the one in the mathematical classification theorem. -/
structure GreedyCertificate {n : ℕ} (s : ℝ) (β : Fin (n + 1) → ℝ)
    (ell rho : Fin n → ℝ) (L : ℝ) where
  pivot : Fin (n + 1) → ℝ
  first : pivot 0 = 1 + s ^ 2 - L / β 0 ^ 2
  step : ∀ j : Fin n, pivot j.succ =
    pivotStep (1 - L / β j.succ ^ 2) (pivot j.castSucc)
      (greedyEndpoint (ell j) (rho j) (pivot j.castSucc))
  positive : ∀ j : Fin n, 0 < pivot j.castSucc
  terminal : pivot (Fin.last n) = 0

/-- The complete endpoint face selected by the greedy pivots. -/
def MinimizingFace {n : ℕ} {s : ℝ} {β : Fin (n + 1) → ℝ}
    {ell rho : Fin n → ℝ} {L : ℝ}
    (C : GreedyCertificate s β ell rho L) (q : Fin n → ℝ) : Prop :=
  Admissible ell rho q ∧ ∀ j, EndpointRule (ell j) (rho j) (C.pivot j.castSucc) (q j)

/-- A ratio vector attains a scalar lower bound through a nonzero scalar vector. -/
def AttainsScalar {n : ℕ} (s : ℝ) (β : Fin (n + 1) → ℝ)
    (q : Fin n → ℝ) (L : ℝ) : Prop :=
  ∃ x : Fin (n + 1) → ℝ, x ≠ 0 ∧ energy s q x = L * mass β x

lemma fin_sum_telescope {n : ℕ} (f : Fin (n + 1) → ℝ) :
    ∑ j : Fin n, (f j.castSucc - f j.succ) = f 0 - f (Fin.last n) := by
  have h₁ := Fin.sum_univ_castSucc f
  have h₂ := Fin.sum_univ_succ f
  rw [Finset.sum_sub_distrib]
  linarith

/-- The exact identity underlying the global optimizer classification. -/
theorem GreedyCertificate.energy_decomposition {n : ℕ} {s : ℝ}
    {β : Fin (n + 1) → ℝ} {ell rho : Fin n → ℝ} {L : ℝ}
    (C : GreedyCertificate s β ell rho L) (q : Fin n → ℝ)
    (x : Fin (n + 1) → ℝ) :
    energy s q x - L * mass β x =
      ∑ j : Fin n,
        (C.pivot j.castSucc * (x j.castSucc - q j / C.pivot j.castSucc * x j.succ) ^ 2 +
          ((q j ^ 2 - (greedyEndpoint (ell j) (rho j) (C.pivot j.castSucc)) ^ 2) *
            (1 - 1 / C.pivot j.castSucc)) * x j.succ ^ 2) := by
  have hlocal (j : Fin n) :
      C.pivot j.castSucc * (x j.castSucc - q j / C.pivot j.castSucc * x j.succ) ^ 2 +
          ((q j ^ 2 - (greedyEndpoint (ell j) (rho j) (C.pivot j.castSucc)) ^ 2) *
            (1 - 1 / C.pivot j.castSucc)) * x j.succ ^ 2 =
      (x j.castSucc - q j * x j.succ) ^ 2 - L * (x j.succ / β j.succ) ^ 2 +
        ((C.pivot j.castSucc - 1) * x j.castSucc ^ 2 -
          (C.pivot j.succ - 1) * x j.succ ^ 2) := by
    rw [C.step j]
    unfold pivotStep
    have hne := ne_of_gt (C.positive j)
    field_simp
    ring
  simp_rw [hlocal]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum]
  rw [fin_sum_telescope (fun i => (C.pivot i - 1) * x i ^ 2)]
  unfold energy mass
  rw [Fin.sum_univ_succ, C.first, C.terminal]
  ring

/-- The certificate gives the literal energy bound throughout the entire box. -/
theorem GreedyCertificate.lower_bound {n : ℕ} {s : ℝ}
    {β : Fin (n + 1) → ℝ} {ell rho : Fin n → ℝ} {L : ℝ}
    (C : GreedyCertificate s β ell rho L) (hell : ∀ j, 0 ≤ ell j) :
    ScalarLowerBound s β ell rho L := by
  intro q hq x
  have h := C.energy_decomposition q x
  have hn : 0 ≤ ∑ j : Fin n,
        (C.pivot j.castSucc * (x j.castSucc - q j / C.pivot j.castSucc * x j.succ) ^ 2 +
          ((q j ^ 2 - (greedyEndpoint (ell j) (rho j) (C.pivot j.castSucc)) ^ 2) *
            (1 - 1 / C.pivot j.castSucc)) * x j.succ ^ 2) := by
    apply Finset.sum_nonneg
    intro j _
    exact add_nonneg (mul_nonneg (le_of_lt (C.positive j)) (sq_nonneg _))
      (mul_nonneg (endpointMismatch_nonneg (hell j) (C.positive j) (hq j).1 (hq j).2)
        (sq_nonneg _))
  linarith

/-- The positive null vector on the minimizing face, normalized by its first coordinate. -/
def GreedyCertificate.groundVector {n : ℕ} {s : ℝ}
    {β : Fin (n + 1) → ℝ} {ell rho : Fin n → ℝ} {L : ℝ}
    (C : GreedyCertificate s β ell rho L) (q : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  Fin.induction 1 (fun j r => C.pivot j.castSucc / q j * r)

@[simp] theorem GreedyCertificate.groundVector_zero {n : ℕ} {s : ℝ}
    {β : Fin (n + 1) → ℝ} {ell rho : Fin n → ℝ} {L : ℝ}
    (C : GreedyCertificate s β ell rho L) (q : Fin n → ℝ) :
    C.groundVector q 0 = 1 := Fin.induction_zero _ _

@[simp] theorem GreedyCertificate.groundVector_succ {n : ℕ} {s : ℝ}
    {β : Fin (n + 1) → ℝ} {ell rho : Fin n → ℝ} {L : ℝ}
    (C : GreedyCertificate s β ell rho L) (q : Fin n → ℝ) (j : Fin n) :
    C.groundVector q j.succ =
      C.pivot j.castSucc / q j * C.groundVector q j.castSucc := Fin.induction_succ _ _ _

theorem GreedyCertificate.groundVector_positive {n : ℕ} {s : ℝ}
    {β : Fin (n + 1) → ℝ} {ell rho : Fin n → ℝ} {L : ℝ}
    (C : GreedyCertificate s β ell rho L) {q : Fin n → ℝ}
    (hq : ∀ j, 0 < q j) (i : Fin (n + 1)) : 0 < C.groundVector q i := by
  induction i using Fin.induction with
  | zero => simp
  | succ j ih =>
    rw [C.groundVector_succ]
    exact mul_pos (div_pos (C.positive j) (hq j)) ih

/-- Every point of the face attains the same bound, through a strictly positive vector. -/
theorem GreedyCertificate.face_attains {n : ℕ} {s : ℝ}
    {β : Fin (n + 1) → ℝ} {ell rho : Fin n → ℝ} {L : ℝ}
    (C : GreedyCertificate s β ell rho L) (hell : ∀ j, 0 < ell j)
    {q : Fin n → ℝ} (hq : MinimizingFace C q) :
    energy s q (C.groundVector q) = L * mass β (C.groundVector q) := by
  have hp (j : Fin n) : 0 < q j := lt_of_lt_of_le (hell j) (hq.1 j).1
  have hr (j : Fin n) :
      C.groundVector q j.castSucc - q j / C.pivot j.castSucc * C.groundVector q j.succ = 0 := by
    rw [C.groundVector_succ]
    field_simp [ne_of_gt (hp j), ne_of_gt (C.positive j)]
    ring
  have hm (j : Fin n) := (endpointMismatch_eq_zero_iff (hell j) (C.positive j)
    (hq.1 j).1 (hq.1 j).2).2 (hq.2 j)
  have hid := C.energy_decomposition q (C.groundVector q)
  simp only [hr, hm, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul, add_zero,
    Finset.sum_const_zero] at hid
  linarith

/-- Vanishing of the sum of nonnegative squares makes every site nonzero. -/
theorem GreedyCertificate.equality_coordinates_nonzero {n : ℕ} {s : ℝ}
    {β : Fin (n + 1) → ℝ} {ell rho : Fin n → ℝ} {L : ℝ}
    (C : GreedyCertificate s β ell rho L) {q : Fin n → ℝ}
    (hq : ∀ j, 0 < q j) {x : Fin (n + 1) → ℝ} (hx : x ≠ 0)
    (hr : ∀ j, x j.castSucc - q j / C.pivot j.castSucc * x j.succ = 0) :
    ∀ i, x i ≠ 0 := by
  have hx0 : x 0 ≠ 0 := by
    intro hz
    apply hx
    funext i
    change x i = 0
    induction i using Fin.induction with
    | zero => exact hz
    | succ j ih =>
      have hh := hr j
      rw [ih, zero_sub, neg_eq_zero] at hh
      exact (mul_eq_zero.mp hh).resolve_left (div_ne_zero (ne_of_gt (hq j)) (ne_of_gt (C.positive j)))
  intro i
  induction i using Fin.induction with
  | zero => exact hx0
  | succ j ih =>
    intro hz
    have hh := hr j
    simp only [hz, mul_zero, sub_zero] at hh
    exact ih hh

/-- Exact scalar classification: all and only the points of one endpoint face attain the bound. -/
theorem GreedyCertificate.attains_iff_face {n : ℕ} {s : ℝ}
    {β : Fin (n + 1) → ℝ} {ell rho : Fin n → ℝ} {L : ℝ}
    (C : GreedyCertificate s β ell rho L) (hell : ∀ j, 0 < ell j)
    {q : Fin n → ℝ} (hq : Admissible ell rho q) :
    AttainsScalar s β q L ↔ MinimizingFace C q := by
  constructor
  · rintro ⟨x, hx, he⟩
    have hn (j : Fin n) := endpointMismatch_nonneg (le_of_lt (hell j))
      (C.positive j) (hq j).1 (hq j).2
    have hid := C.energy_decomposition q x
    have hz : ∀ j : Fin n,
        C.pivot j.castSucc * (x j.castSucc - q j / C.pivot j.castSucc * x j.succ) ^ 2 +
          ((q j ^ 2 - (greedyEndpoint (ell j) (rho j) (C.pivot j.castSucc)) ^ 2) *
            (1 - 1 / C.pivot j.castSucc)) * x j.succ ^ 2 = 0 := by
      intro j
      apply (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ) (fun k _ =>
        add_nonneg (mul_nonneg (le_of_lt (C.positive k))
          (sq_nonneg (x k.castSucc - q k / C.pivot k.castSucc * x k.succ)))
          (mul_nonneg (hn k) (sq_nonneg (x k.succ))))).1 ?_ j (Finset.mem_univ j)
      linarith
    have hr (j : Fin n) : x j.castSucc - q j / C.pivot j.castSucc * x j.succ = 0 := by
      have hh := hz j
      have h₂ := mul_nonneg (hn j) (sq_nonneg (x j.succ))
      have h₁ : C.pivot j.castSucc * (x j.castSucc - q j / C.pivot j.castSucc * x j.succ) ^ 2 = 0 := by
        have hh' := mul_nonneg (le_of_lt (C.positive j))
          (sq_nonneg (x j.castSucc - q j / C.pivot j.castSucc * x j.succ))
        linarith
      have hh' := (mul_eq_zero.mp h₁).resolve_left (ne_of_gt (C.positive j))
      exact sq_eq_zero_iff.mp hh'
    have hxn := C.equality_coordinates_nonzero
      (fun j => lt_of_lt_of_le (hell j) (hq j).1) hx hr
    refine ⟨hq, fun j => ?_⟩
    apply (endpointMismatch_eq_zero_iff (hell j) (C.positive j) (hq j).1 (hq j).2).1
    have hh := hz j
    rw [hr j] at hh
    simp only [zero_pow (by decide : 2 ≠ 0), mul_zero, zero_add] at hh
    exact (mul_eq_zero.mp hh).resolve_right (pow_ne_zero 2 (hxn j.succ))
  · intro hf
    refine ⟨C.groundVector q, ?_, C.face_attains hell hf⟩
    intro hz
    have hh := congrFun hz 0
    simp at hh


/-- A nonnegative equality vector has strictly positive coordinates. -/
theorem GreedyCertificate.equality_positive {n : ℕ} {s : ℝ}
    {β : Fin (n + 1) → ℝ} {ell rho : Fin n → ℝ} {L : ℝ}
    (C : GreedyCertificate s β ell rho L) (hell : ∀ j, 0 < ell j)
    {q : Fin n → ℝ} (hq : Admissible ell rho q)
    {x : Fin (n + 1) → ℝ} (hx : x ≠ 0) (hxn : ∀ i, 0 ≤ x i)
    (he : energy s q x = L * mass β x) : ∀ i, 0 < x i := by
  have hn (j : Fin n) := endpointMismatch_nonneg (le_of_lt (hell j))
    (C.positive j) (hq j).1 (hq j).2
  have hid := C.energy_decomposition q x
  have hz : ∀ j : Fin n,
      C.pivot j.castSucc * (x j.castSucc - q j / C.pivot j.castSucc * x j.succ) ^ 2 +
        ((q j ^ 2 - (greedyEndpoint (ell j) (rho j) (C.pivot j.castSucc)) ^ 2) *
          (1 - 1 / C.pivot j.castSucc)) * x j.succ ^ 2 = 0 := by
    intro j
    apply (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ) (fun k _ =>
      add_nonneg (mul_nonneg (le_of_lt (C.positive k))
        (sq_nonneg (x k.castSucc - q k / C.pivot k.castSucc * x k.succ)))
        (mul_nonneg (hn k) (sq_nonneg (x k.succ))))).1 ?_ j (Finset.mem_univ j)
    linarith
  have hr (j : Fin n) : x j.castSucc - q j / C.pivot j.castSucc * x j.succ = 0 := by
    have hh := hz j
    have h₂ := mul_nonneg (hn j) (sq_nonneg (x j.succ))
    have h₁ : C.pivot j.castSucc * (x j.castSucc - q j / C.pivot j.castSucc * x j.succ) ^ 2 = 0 := by
      have hh' := mul_nonneg (le_of_lt (C.positive j))
        (sq_nonneg (x j.castSucc - q j / C.pivot j.castSucc * x j.succ))
      linarith
    exact sq_eq_zero_iff.mp ((mul_eq_zero.mp h₁).resolve_left (ne_of_gt (C.positive j)))
  have hne := C.equality_coordinates_nonzero
    (fun j => lt_of_lt_of_le (hell j) (hq j).1) hx hr
  exact fun i => lt_of_le_of_ne (hxn i) (Ne.symm (hne i))

/-- The ordered-pivot property that rules out disconnected optimizer faces. -/
theorem GreedyCertificate.pivot_below_one {n : ℕ} {s : ℝ}
    {β : Fin (n + 1) → ℝ} {ell rho : Fin n → ℝ} {L : ℝ}
    (C : GreedyCertificate s β ell rho L) (hβ : ∀ i, 0 < β i) (hL : 0 < L)
    {i j : Fin (n + 1)} (hij : i < j) (hi : C.pivot i ≤ 1) : C.pivot j < 1 := by
  induction j using Fin.induction with
  | zero => exact False.elim (by simp at hij)
  | succ j ih =>
    rw [C.step j]
    apply pivotStep_lt_one (by have hp := div_pos hL (sq_pos_of_pos (hβ j.succ)); linarith)
      (C.positive j)
    have hij' : i ≤ j.castSucc := by simpa [Fin.le_iff_val_le_val, Fin.lt_def] using hij
    rcases lt_or_eq_of_le hij' with h | h
    · exact le_of_lt (ih h)
    · simpa [← h] using hi

/-- There is at most one free coordinate. -/
theorem GreedyCertificate.tie_unique {n : ℕ} {s : ℝ}
    {β : Fin (n + 1) → ℝ} {ell rho : Fin n → ℝ} {L : ℝ}
    (C : GreedyCertificate s β ell rho L) (hβ : ∀ i, 0 < β i) (hL : 0 < L)
    {i j : Fin n} (hi : C.pivot i.castSucc = 1) (hj : C.pivot j.castSucc = 1) : i = j := by
  rcases lt_trichotomy i j with h | h | h
  · have hh := C.pivot_below_one hβ hL (Fin.castSucc_lt_castSucc_iff.mpr h) (le_of_eq hi)
    linarith
  · exact h
  · have hh := C.pivot_below_one hβ hL (Fin.castSucc_lt_castSucc_iff.mpr h) (le_of_eq hj)
    linarith

/-- Away from a tie, the endpoint rule fixes the coordinate uniquely. -/
lemma endpointRule_iff_greedy {ell rho a q : ℝ} (ha : a ≠ 1) :
    EndpointRule ell rho a q ↔ q = greedyEndpoint ell rho a := by
  rcases lt_or_gt_of_ne ha with h | h
  · simp only [EndpointRule, greedyEndpoint, not_le.mpr h, ↓reduceIte]
    constructor
    · exact fun hh => hh.2 h
    · intro hh
      exact ⟨by intro hc; linarith, fun _ => hh⟩
  · simp only [EndpointRule, greedyEndpoint, le_of_lt h, ↓reduceIte]
    constructor
    · exact fun hh => hh.1 h
    · intro hh
      exact ⟨fun _ => hh, by intro hc; linarith⟩

/-- The complete minimizing face is a single vertex or a single full box edge.
Degenerate intervals are retained, so the edge alternative may collapse to a point. -/
theorem GreedyCertificate.face_vertex_or_edge {n : ℕ} {s : ℝ}
    {β : Fin (n + 1) → ℝ} {ell rho : Fin n → ℝ} {L : ℝ}
    (C : GreedyCertificate s β ell rho L) (hβ : ∀ i, 0 < β i) (hL : 0 < L)
    (hbox : ∀ j, ell j ≤ rho j) :
    (∃ v : Fin n → ℝ, Admissible ell rho v ∧
      ∀ q, MinimizingFace C q ↔ q = v) ∨
    (∃ k : Fin n, ∀ q, MinimizingFace C q ↔
      Admissible ell rho q ∧ ∀ j, j ≠ k →
        q j = greedyEndpoint (ell j) (rho j) (C.pivot j.castSucc)) := by
  classical
  by_cases ht : ∃ k : Fin n, C.pivot k.castSucc = 1
  · obtain ⟨k, hk⟩ := ht
    right
    refine ⟨k, fun q => ?_⟩
    constructor
    · rintro ⟨hq, hr⟩
      refine ⟨hq, fun j hj => ?_⟩
      exact (endpointRule_iff_greedy (fun he => hj (C.tie_unique hβ hL he hk))).1 (hr j)
    · rintro ⟨hq, hr⟩
      refine ⟨hq, fun j => ?_⟩
      by_cases hj : j = k
      · subst j
        simp [EndpointRule, hk]
      · exact (endpointRule_iff_greedy (fun he => hj (C.tie_unique hβ hL he hk))).2 (hr j hj)
  · left
    let v : Fin n → ℝ := fun j => greedyEndpoint (ell j) (rho j) (C.pivot j.castSucc)
    have hv : Admissible ell rho v := fun j => greedyEndpoint_mem (hbox j)
    refine ⟨v, hv, fun q => ?_⟩
    have hne (j : Fin n) : C.pivot j.castSucc ≠ 1 := fun h => ht ⟨j, h⟩
    constructor
    · rintro ⟨hq, hr⟩
      funext j
      exact (endpointRule_iff_greedy (hne j)).1 (hr j)
    · intro he
      subst q
      exact ⟨hv, fun j => (endpointRule_iff_greedy (hne j)).2 rfl⟩

end ChiralGap
