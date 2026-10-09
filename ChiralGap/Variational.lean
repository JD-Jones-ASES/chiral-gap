module

public import ChiralGap.Basic

public section

namespace ChiralGap

lemma mass_eq_zero_iff {n : ℕ} {β x : Fin (n + 1) → ℝ}
    (hβ : ∀ i, β i ≠ 0) : mass β x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have hz := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i (_ : i ∈ Finset.univ) => sq_nonneg (x i / β i))).mp h
    funext i
    have hi := (sq_eq_zero_iff.mp (hz i (Finset.mem_univ i)))
    simpa [hβ i] using hi
  · rintro rfl
    simp

lemma mass_pos {n : ℕ} {β x : Fin (n + 1) → ℝ}
    (hβ : ∀ i, β i ≠ 0) (hx : x ≠ 0) : 0 < mass β x :=
  lt_of_le_of_ne (mass_nonneg β x) (Ne.symm (mt (mass_eq_zero_iff hβ).mp hx))

lemma energy_eq_zero_iff {n : ℕ} {s : ℝ} {q : Fin n → ℝ}
    {x : Fin (n + 1) → ℝ} : energy s q x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have hs : 0 ≤ s ^ 2 * x 0 ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
    have hr : 0 ≤ ∑ j : Fin n, (x j.castSucc - q j * x j.succ) ^ 2 :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hl : x (Fin.last n) = 0 := by
      have : x (Fin.last n) ^ 2 = 0 := by unfold energy at h; nlinarith [sq_nonneg (x (Fin.last n))]
      exact sq_eq_zero_iff.mp this
    have he : ∀ j : Fin n, x j.castSucc - q j * x j.succ = 0 := by
      intro j
      have hj : (x j.castSucc - q j * x j.succ) ^ 2 ≤
          ∑ k : Fin n, (x k.castSucc - q k * x k.succ) ^ 2 :=
        Finset.single_le_sum (fun k _ => sq_nonneg (x k.castSucc - q k * x k.succ)) (Finset.mem_univ j)
      have : (x j.castSucc - q j * x j.succ) ^ 2 = 0 := by
        unfold energy at h
        nlinarith [sq_nonneg (x (Fin.last n)), sq_nonneg (x j.castSucc - q j * x j.succ)]
      exact sq_eq_zero_iff.mp this
    funext i
    exact Fin.reverseInduction hl (fun j ih => by simpa [ih] using he j) i
  · rintro rfl
    simp

lemma energy_pos {n : ℕ} {s : ℝ} {q : Fin n → ℝ}
    {x : Fin (n + 1) → ℝ} (hx : x ≠ 0) : 0 < energy s q x :=
  lt_of_le_of_ne (energy_nonneg s q x) (Ne.symm (mt energy_eq_zero_iff.mp hx))

lemma mass_mul {n : ℕ} (β x : Fin (n + 1) → ℝ) (c : ℝ) :
    mass β (fun i => c * x i) = c ^ 2 * mass β x := by
  simp [mass, mul_div_assoc, mul_pow, Finset.mul_sum]

lemma energy_mul {n : ℕ} (s : ℝ) (q : Fin n → ℝ)
    (x : Fin (n + 1) → ℝ) (c : ℝ) :
    energy s q (fun i => c * x i) = c ^ 2 * energy s q x := by
  unfold energy
  have hr : ∀ j : Fin n,
      (c * x j.castSucc - q j * (c * x j.succ)) ^ 2 =
      c ^ 2 * (x j.castSucc - q j * x j.succ) ^ 2 := by intro j; ring
  simp_rw [hr]
  rw [← Finset.mul_sum]
  ring

lemma continuous_mass {n : ℕ} (β : Fin (n + 1) → ℝ) : Continuous (mass β) := by
  unfold mass
  fun_prop

lemma continuous_energy {n : ℕ} (s : ℝ) :
    Continuous (fun p : (Fin n → ℝ) × (Fin (n + 1) → ℝ) => energy s p.1 p.2) := by
  unfold energy
  fun_prop

lemma isCompact_mass_one {n : ℕ} (β : Fin (n + 1) → ℝ)
    (hβ : ∀ i, β i ≠ 0) :
    IsCompact {x | mass β x = 1} := by
  have hbox : IsCompact {x : Fin (n + 1) → ℝ | ∀ i, x i ∈ Set.Icc (-|β i|) |β i|} :=
    isCompact_pi_infinite (fun i => isCompact_Icc)
  apply hbox.of_isClosed_subset (isClosed_eq (continuous_mass β) continuous_const)
  intro x hx i
  have hi : (x i / β i) ^ 2 ≤ 1 := by
    calc
      _ ≤ mass β x := Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ i)
      _ = 1 := hx
  have hb := hβ i
  have hsq : x i ^ 2 ≤ β i ^ 2 := by
      have hp : 0 < β i ^ 2 := sq_pos_of_ne_zero hb
      rw [div_pow, div_le_one hp] at hi
      exact hi
  have habs : |x i| ≤ |β i| := abs_le_of_sq_le_sq (by simpa only [sq_abs] using hsq) (abs_nonneg _)
  exact abs_le.mp habs

lemma mass_one_nonempty {n : ℕ} (β : Fin (n + 1) → ℝ)
    (hβ : ∀ i, β i ≠ 0) : ({x | mass β x = 1} : Set (Fin (n + 1) → ℝ)).Nonempty := by
  refine ⟨Pi.single 0 (β 0), ?_⟩
  classical
  simp [mass, Pi.single_apply, ite_div, hβ 0]

lemma normalize_mass {n : ℕ} {β x : Fin (n + 1) → ℝ}
    (hβ : ∀ i, β i ≠ 0) (hx : x ≠ 0) :
    mass β (fun i => (Real.sqrt (mass β x))⁻¹ * x i) = 1 := by
  rw [mass_mul, inv_pow, Real.sq_sqrt (mass_nonneg β x)]
  exact inv_mul_cancel₀ (ne_of_gt (mass_pos hβ hx))

lemma normalize_energy {n : ℕ} (s : ℝ) (q : Fin n → ℝ)
    (β x : Fin (n + 1) → ℝ) :
    energy s q (fun i => (Real.sqrt (mass β x))⁻¹ * x i) = energy s q x / mass β x := by
  rw [energy_mul, inv_pow, Real.sq_sqrt (mass_nonneg β x)]
  ring

/-- The actual continuous box optimization attains a strictly positive value.
No nonnegativity of the ratios is needed for this existence statement. -/
theorem exists_scalar_optimum {n : ℕ} (s : ℝ) (β : Fin (n + 1) → ℝ)
    (ell rho : Fin n → ℝ) (hβ : ∀ i, 0 < β i) (hbox : ∀ j, ell j ≤ rho j) :
    ∃ L, 0 < L ∧ ScalarLowerBound s β ell rho L ∧
      ∃ q x, Admissible ell rho q ∧ mass β x = 1 ∧ energy s q x = L := by
  have hb : ∀ i, β i ≠ 0 := fun i => ne_of_gt (hβ i)
  have hc : IsCompact {q | Admissible ell rho q} :=
    isCompact_pi_infinite (fun j => isCompact_Icc)
  have hn : ({q | Admissible ell rho q} : Set (Fin n → ℝ)).Nonempty :=
    ⟨ell, fun j => ⟨le_rfl, hbox j⟩⟩
  obtain ⟨⟨q, x⟩, ⟨hq, hx⟩, hmin⟩ :=
    (hc.prod (isCompact_mass_one β hb)).exists_isMinOn
      (hn.prod (mass_one_nonempty β hb)) (continuous_energy s).continuousOn
  have hx0 : x ≠ 0 := by intro hz; simp [hz] at hx
  refine ⟨energy s q x, energy_pos hx0, ?_, q, x, hq, hx, rfl⟩
  intro r hr y
  by_cases hy : y = 0
  · simp [hy]
  · have hn := normalize_mass hb hy
    have he := hmin (show (r, fun i => (Real.sqrt (mass β y))⁻¹ * y i) ∈
        {q | Admissible ell rho q} ×ˢ {x | mass β x = 1} from ⟨hr, hn⟩)
    change energy s q x ≤ energy s r (fun i => (Real.sqrt (mass β y))⁻¹ * y i) at he
    rw [normalize_energy] at he
    exact (le_div_iff₀ (mass_pos hb hy)).mp he

/-- Worst squared scalar gap, defined by the literal residual energy on the
weighted unit sphere. Theorems below establish attainment and positivity. -/
@[expose] noncomputable def robustMinimum {n : ℕ} (s : ℝ) (β : Fin (n + 1) → ℝ)
    (ell rho : Fin n → ℝ) : ℝ :=
  sInf {t | ∃ q x, Admissible ell rho q ∧ mass β x = 1 ∧ energy s q x = t}

theorem robustMinimum_spec {n : ℕ} (s : ℝ) (β : Fin (n + 1) → ℝ)
    (ell rho : Fin n → ℝ) (hβ : ∀ i, 0 < β i) (hbox : ∀ j, ell j ≤ rho j) :
    0 < robustMinimum s β ell rho ∧ ScalarLowerBound s β ell rho (robustMinimum s β ell rho) ∧
      ∃ q x, Admissible ell rho q ∧ mass β x = 1 ∧ energy s q x = robustMinimum s β ell rho := by
  obtain ⟨L, hpos, hlower, q, x, hq, hx, he⟩ := exists_scalar_optimum s β ell rho hβ hbox
  have hb : BddBelow {t | ∃ q x, Admissible ell rho q ∧ mass β x = 1 ∧ energy s q x = t} := by
    refine ⟨0, ?_⟩
    rintro t ⟨r, y, _, _, rfl⟩
    exact energy_nonneg s r y
  have hmem : L ∈ {t | ∃ q x, Admissible ell rho q ∧ mass β x = 1 ∧ energy s q x = t} :=
    ⟨q, x, hq, hx, he⟩
  have heq : robustMinimum s β ell rho = L := by
    apply le_antisymm (csInf_le hb hmem)
    apply le_csInf ⟨L, hmem⟩
    rintro t ⟨r, y, hr, hy, ht⟩
    have := hlower r hr y
    simpa [hy, ht] using this
  rw [heq]
  exact ⟨hpos, hlower, q, x, hq, hx, he⟩

end ChiralGap
