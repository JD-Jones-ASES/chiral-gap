module


public import Mathlib


@[expose] public section


noncomputable section


/-! Independent problem statement. Every model definition below is complete.
Only the designated theorem statements contain placeholders. -/


namespace ChiralGap

open scoped Matrix

open Module Module.End

abbrev firstSite (n : ℕ) : Fin (n + 1) := ⟨0, Nat.zero_lt_succ n⟩

@[simp] theorem firstSite_eq_zero (n : ℕ) : firstSite n = 0 := rfl

def energy {n : ℕ} (s : ℝ) (q : Fin n → ℝ) (x : Fin (n + 1) → ℝ) : ℝ :=
  s ^ 2 * x 0 ^ 2 + ∑ j, (x j.castSucc - q j * x j.succ) ^ 2 +
    x (Fin.last n) ^ 2

def mass {n : ℕ} (β x : Fin (n + 1) → ℝ) : ℝ :=
  ∑ i, (x i / β i) ^ 2

def Admissible {n : ℕ} (ell rho q : Fin n → ℝ) : Prop :=
  ∀ j, ell j ≤ q j ∧ q j ≤ rho j

def candidate {n : ℕ} (ell rho : Fin n → ℝ) (k : Fin (n + 1)) : Fin n → ℝ :=
  fun j => if j.val < k.val then ell j else rho j

def ScalarLowerBound {n : ℕ} (s : ℝ) (β : Fin (n + 1) → ℝ)
    (ell rho : Fin n → ℝ) (L : ℝ) : Prop :=
  ∀ q, Admissible ell rho q → ∀ x, L * mass β x ≤ energy s q x

noncomputable def robustMinimum {n : ℕ} (s : ℝ) (β : Fin (n + 1) → ℝ)
    (ell rho : Fin n → ℝ) : ℝ :=
  sInf {t | ∃ q x, Admissible ell rho q ∧ mass β x = 1 ∧ energy s q x = t}

noncomputable def scalarGap {n : ℕ} (s : ℝ) (β : Fin (n + 1) → ℝ) (q : Fin n → ℝ) : ℝ :=
  robustMinimum s β q q

def pivotStep (d a q : ℝ) : ℝ := d + q ^ 2 * (1 - 1 / a)

def greedyEndpoint (ell rho a : ℝ) : ℝ := if 1 ≤ a then ell else rho

def EndpointRule (ell rho a q : ℝ) : Prop :=
  (1 < a → q = ell) ∧ (a < 1 → q = rho)

structure GreedyCertificate {n : ℕ} (s : ℝ) (β : Fin (n + 1) → ℝ)
    (ell rho : Fin n → ℝ) (L : ℝ) where
  pivot : Fin (n + 1) → ℝ
  first : pivot 0 = 1 + s ^ 2 - L / β 0 ^ 2
  step : ∀ j : Fin n, pivot j.succ =
    pivotStep (1 - L / β j.succ ^ 2) (pivot j.castSucc)
      (greedyEndpoint (ell j) (rho j) (pivot j.castSucc))
  positive : ∀ j : Fin n, 0 < pivot j.castSucc
  terminal : pivot (Fin.last n) = 0

def MinimizingFace {n : ℕ} {s : ℝ} {β : Fin (n + 1) → ℝ}
    {ell rho : Fin n → ℝ} {L : ℝ}
    (C : GreedyCertificate s β ell rho L) (q : Fin n → ℝ) : Prop :=
  Admissible ell rho q ∧ ∀ j, EndpointRule (ell j) (rho j) (C.pivot j.castSucc) (q j)

def ScalarMinimizer {n : ℕ} (s : ℝ) (β : Fin (n + 1) → ℝ)
    (ell rho q : Fin n → ℝ) : Prop :=
  Admissible ell rho q ∧ scalarGap s β q = robustMinimum s β ell rho

abbrev ResidualRow (n : ℕ) := Unit ⊕ (Fin n ⊕ Unit)

def residualMatrix {n : ℕ} (s : ℝ) (β : Fin (n + 1) → ℝ) (q : Fin n → ℝ) :
    Matrix (ResidualRow n) (Fin (n + 1)) ℝ := fun r =>
  match r with
  | .inl _ => Pi.single (firstSite n) (s * β (firstSite n))
  | .inr (.inl j) =>
      Pi.single j.castSucc (β j.castSucc) - Pi.single j.succ (q j * β j.succ)
  | .inr (.inr _) => Pi.single (Fin.last n) (β (Fin.last n))

def gram {n : ℕ} (s : ℝ) (β : Fin (n + 1) → ℝ) (q : Fin n → ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  (residualMatrix s β q).transpose * residualMatrix s β q

theorem robustMinimum_spec {n : ℕ} (s : ℝ) (β : Fin (n + 1) → ℝ)
    (ell rho : Fin n → ℝ) (hβ : ∀ i, 0 < β i) (hbox : ∀ j, ell j ≤ rho j) :
    0 < robustMinimum s β ell rho ∧ ScalarLowerBound s β ell rho (robustMinimum s β ell rho) ∧
      ∃ q x, Admissible ell rho q ∧ mass β x = 1 ∧ energy s q x = robustMinimum s β ell rho := by
  sorry

theorem one_switch_value {n : ℕ} (s : ℝ) (β : Fin (n + 1) → ℝ)
    (ell rho : Fin n → ℝ) (hβ : ∀ i, 0 < β i) (hell : ∀ j, 0 ≤ ell j)
    (hbox : ∀ j, ell j ≤ rho j) :
    robustMinimum s β ell rho =
      Finset.univ.inf' Finset.univ_nonempty (fun k : Fin (n + 1) => scalarGap s β (candidate ell rho k)) := by
  sorry

theorem two_certificate_value {n : ℕ} (s : ℝ) (β : Fin (n + 2) → ℝ)
    (rho : Fin (n + 1) → ℝ) (hβ : ∀ i, 0 < β i) (hr : ∀ j, 0 ≤ rho j) :
    robustMinimum s β 0 rho =
      min (scalarGap s β rho) (scalarGap 0 (Fin.tail β) (Fin.tail rho)) := by
  sorry

theorem scalarGap_eigenvector {n : ℕ} (s : ℝ) (β : Fin (n + 1) → ℝ)
    (q : Fin n → ℝ) (hβ : ∀ i, 0 < β i) :
    ∃ y : Fin (n + 1) → ℝ, (∑ i, y i ^ 2) = 1 ∧
      gram s β q *ᵥ y = scalarGap s β q • y := by
  sorry

theorem scalarGap_le_eigenvalue {n : ℕ} (s : ℝ) (β : Fin (n + 1) → ℝ)
    (q : Fin n → ℝ) (hβ : ∀ i, 0 < β i) (t : ℝ)
    {y : Fin (n + 1) → ℝ} (hy : y ≠ 0) (he : gram s β q *ᵥ y = t • y) :
    scalarGap s β q ≤ t := by
  sorry

theorem scalar_optimizer_classification {n : ℕ} (s : ℝ) (β : Fin (n + 1) → ℝ)
    (ell rho : Fin n → ℝ) (hβ : ∀ i, 0 < β i)
    (hl : ∀ j, 0 < ell j) (horder : ∀ j, ell j ≤ rho j) :
    ∃ C : GreedyCertificate s β ell rho (robustMinimum s β ell rho),
      (∀ q, ScalarMinimizer s β ell rho q ↔ MinimizingFace C q) ∧
      (∀ i j : Fin n, C.pivot i.castSucc = 1 → C.pivot j.castSucc = 1 → i = j) := by
  sorry

theorem scalar_minimizers_vertex_or_edge {n : ℕ} (s : ℝ) (β : Fin (n + 1) → ℝ)
    (ell rho : Fin n → ℝ) (hβ : ∀ i, 0 < β i)
    (hl : ∀ j, 0 < ell j) (horder : ∀ j, ell j ≤ rho j) :
    (∃ k : Fin (n + 1), ∀ q, ScalarMinimizer s β ell rho q ↔ q = candidate ell rho k) ∨
    (∃ k : Fin n, ∀ q, ScalarMinimizer s β ell rho q ↔
      Admissible ell rho q ∧
        (∀ j, j < k → q j = ell j) ∧ (∀ j, k < j → q j = rho j)) := by
  sorry

section ChannelDefinitions

variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

def channelEnergy (R : Fin (n + 1) → V →ₗ[ℂ] V)
    (B : Fin (n + 1) → V ≃ₗ[ℂ] V) (y : Fin (n + 1) → V) : ℝ :=
  ‖R (firstSite n) (B (firstSite n) (y (firstSite n)))‖ ^ 2 +
    ∑ j : Fin n, ‖B j.castSucc (y j.castSucc) + R j.succ (B j.succ (y j.succ))‖ ^ 2
    + ‖B (Fin.last n) (y (Fin.last n))‖ ^ 2

def channelMass (y : Fin (n + 1) → V) : ℝ := ∑ i, ‖y i‖ ^ 2

def AttainsChannel (R : Fin (n + 1) → V →ₗ[ℂ] V)
    (B : Fin (n + 1) → V ≃ₗ[ℂ] V) (L : ℝ) : Prop :=
  ∃ y : Fin (n + 1) → V, y ≠ 0 ∧ channelEnergy R B y = L * channelMass y

end ChannelDefinitions

section SpectralDefinitions

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F]

noncomputable def finiteAdjoint (A : E →ₗ[ℂ] F) : F →ₗ[ℂ] E := A.adjoint

noncomputable def chiral (A : E →ₗ[ℂ] F) : (F × E) →ₗ[ℂ] (F × E) :=
  (A.comp (LinearMap.snd ℂ F E)).prod ((finiteAdjoint A).comp (LinearMap.fst ℂ F E))

theorem chiral_eigenbasis (A : E →ₗ[ℂ] F) :
    ∃ (b : Basis (Fin (finrank ℂ (WithLp 2 (F × E)))) ℂ (F × E))
      (t : Fin (finrank ℂ (WithLp 2 (F × E))) → ℝ),
      ∀ i, chiral A (b i) = (t i : ℂ) • b i := by
  sorry

end SpectralDefinitions

theorem complexIdentityComposition :
    RingHomCompTriple (RingHom.id ℂ) (RingHom.id ℂ) (RingHom.id ℂ) := inferInstance

theorem complexScalarCommutes {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] :
    SMulCommClass ℂ ℂ W := inferInstance

section HilbertChannels

variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

abbrev ChannelSpace (m : ℕ) (V : Type*) := PiLp 2 (fun _ : Fin m => V)

noncomputable def hopping (R : Fin (n + 1) → V →ₗ[ℂ] V)
    (B : Fin (n + 1) → V ≃ₗ[ℂ] V) :
    ChannelSpace (n + 1) V →ₗ[ℂ] ChannelSpace (n + 2) V where
  toFun y := WithLp.toLp 2 (Fin.cases (R (firstSite n) (B (firstSite n) (y (firstSite n))))
    (Fin.lastCases (B (Fin.last n) (y (Fin.last n)))
      (fun j => B j.castSucc (y j.castSucc) + R j.succ (B j.succ (y j.succ)))))
  map_add' y z := by
    apply PiLp.ext
    intro k
    refine Fin.cases ?_ (fun i => Fin.lastCases ?_ (fun j => ?_) i) k <;>
      simp [map_add, add_add_add_comm, -Fin.succ_last]
  map_smul' a y := by
    apply PiLp.ext
    intro k
    refine Fin.cases ?_ (fun i => Fin.lastCases ?_ (fun j => ?_) i) k <;>
      simp [map_smul, smul_add, -Fin.succ_last]

variable [FiniteDimensional ℂ V]

noncomputable def strongSubspace (B : V ≃ₗ[ℂ] V) (b : ℝ) : Submodule ℂ V :=
  letI : RingHomCompTriple (RingHom.id ℂ) (RingHom.id ℂ) (RingHom.id ℂ) := complexIdentityComposition
  letI : SMulCommClass ℂ ℂ V := complexScalarCommutes
  (B.toLinearMap.comp (finiteAdjoint B.toLinearMap) - ((b ^ 2 : ℝ) : ℂ) • LinearMap.id).ker

noncomputable def boundarySubspace (R : V →ₗ[ℂ] V) (s : ℝ) : Submodule ℂ V :=
  letI : RingHomCompTriple (RingHom.id ℂ) (RingHom.id ℂ) (RingHom.id ℂ) := complexIdentityComposition
  letI : SMulCommClass ℂ ℂ V := complexScalarCommutes
  ((finiteAdjoint R).comp R - ((s ^ 2 : ℝ) : ℂ) • LinearMap.id).ker

omit [FiniteDimensional ℂ V] in
theorem robust_hopping_bound {s : ℝ} {β : Fin (n + 1) → ℝ}
    {ell rho : Fin n → ℝ} (hs : 0 ≤ s) (hβ : ∀ i, 0 < β i)
    (hbox : ∀ j, ell j ≤ rho j)
    (R : Fin (n + 1) → V →ₗ[ℂ] V) (B : Fin (n + 1) → V ≃ₗ[ℂ] V)
    (hB : ∀ i v, β i * ‖v‖ ≤ ‖B i v‖)
    (hfirst : ∀ v, s * ‖v‖ ≤ ‖R 0 v‖)
    (hl : ∀ j v, ell j * ‖v‖ ≤ ‖R j.succ v‖)
    (hu : ∀ j v, ‖R j.succ v‖ ≤ rho j * ‖v‖)
    (y : ChannelSpace (n + 1) V) :
    robustMinimum s β ell rho * ‖y‖ ^ 2 ≤ ‖hopping R B y‖ ^ 2 := by
  sorry

theorem hopping_chiral_zero_multiplicity (R : Fin (n + 1) → V →ₗ[ℂ] V)
    (B : Fin (n + 1) → V ≃ₗ[ℂ] V) :
    finrank ℂ (chiral (hopping R B)).ker = finrank ℂ V := by
  sorry

theorem robust_chiral_sharpness_constrained [Nontrivial V]
    (s : ℝ) (β : Fin (n + 1) → ℝ) (ell rho : Fin n → ℝ)
    (hs : 0 ≤ s) (hβ : ∀ i, 0 < β i)
    (hell : ∀ j, 0 ≤ ell j) (hbox : ∀ j, ell j ≤ rho j) :
    ∃ (R : Fin (n + 1) → V →ₗ[ℂ] V) (B : Fin (n + 1) → V ≃ₗ[ℂ] V),
      (∀ i v, β i * ‖v‖ ≤ ‖B i v‖) ∧
      (∀ v, s * ‖v‖ ≤ ‖R 0 v‖) ∧
      (∀ j v, ell j * ‖v‖ ≤ ‖R j.succ v‖) ∧
      (∀ j v, ‖R j.succ v‖ ≤ rho j * ‖v‖) ∧
      Module.End.HasEigenvalue (chiral (hopping R B))
        (Real.sqrt (robustMinimum s β ell rho) : ℂ) ∧
      Module.End.HasEigenvalue (chiral (hopping R B))
        (-(Real.sqrt (robustMinimum s β ell rho) : ℂ)) := by
  sorry

theorem hopping_nonzero_spectrum (R : Fin (n + 1) → V →ₗ[ℂ] V)
    (B : Fin (n + 1) → V ≃ₗ[ℂ] V) {μ : ℂ} (hμ : μ ≠ 0) :
    Module.End.HasEigenvalue (chiral (hopping R B)) μ ↔
      ∃ i : ℕ, i < (n + 1) * Module.finrank ℂ V ∧
        (μ = ((hopping R B).singularValues i : ℂ) ∨
          μ = -((hopping R B).singularValues i : ℂ)) := by
  sorry

theorem robust_chiral_complex_gap {s : ℝ} {β : Fin (n + 1) → ℝ}
    {ell rho : Fin n → ℝ} (hs : 0 ≤ s) (hβ : ∀ i, 0 < β i)
    (hbox : ∀ j, ell j ≤ rho j)
    (R : Fin (n + 1) → V →ₗ[ℂ] V) (B : Fin (n + 1) → V ≃ₗ[ℂ] V)
    (hB : ∀ i v, β i * ‖v‖ ≤ ‖B i v‖)
    (hfirst : ∀ v, s * ‖v‖ ≤ ‖R 0 v‖)
    (hl : ∀ j v, ell j * ‖v‖ ≤ ‖R j.succ v‖)
    (hu : ∀ j v, ‖R j.succ v‖ ≤ rho j * ‖v‖)
    {μ : ℂ} (hμ : μ ≠ 0) (he : Module.End.HasEigenvalue (chiral (hopping R B)) μ) :
    Real.sqrt (robustMinimum s β ell rho) ≤ ‖μ‖ := by
  sorry

theorem matrix_equality_criterion (s : ℝ) (β : Fin (n + 1) → ℝ)
    (ell rho : Fin n → ℝ) (hs : 0 ≤ s) (hβ : ∀ i, 0 < β i)
    (hell : ∀ j, 0 < ell j) (hbox : ∀ j, ell j ≤ rho j)
    (R : Fin (n + 1) → V →ₗ[ℂ] V) (B : Fin (n + 1) → V ≃ₗ[ℂ] V)
    (hB : ∀ i v, β i * ‖v‖ ≤ ‖B i v‖)
    (hfirst : ∀ v, s * ‖v‖ ≤ ‖R 0 v‖)
    (hl : ∀ j v, ell j * ‖v‖ ≤ ‖R j.succ v‖)
    (hu : ∀ j v, ‖R j.succ v‖ ≤ rho j * ‖v‖) :
    AttainsChannel R B (robustMinimum s β ell rho) ↔
      ∃ q, ScalarMinimizer s β ell rho q ∧ ∃ u : Fin (n + 1) → V,
        (∀ i, ‖u i‖ = 1) ∧ (∀ i, u i ∈ strongSubspace (B i) (β i)) ∧
        u 0 ∈ boundarySubspace (R 0) s ∧
        ∀ j, R j.succ (u j.succ) = -(q j : ℂ) • u j.castSucc := by
  sorry

end HilbertChannels

end ChiralGap
