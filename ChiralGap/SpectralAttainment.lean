module

public import ChiralGap.Spectral

public section

namespace ChiralGap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F]

/-- Equality in a global singular-value bound gives an actual Gram eigenvector. -/
theorem gram_eq_of_norm_attainment (A : E →ₗ[ℂ] F) {L : ℝ}
    (hbound : ∀ z, L * ‖z‖ ^ 2 ≤ ‖A z‖ ^ 2) (y : E)
    (heq : ‖A y‖ ^ 2 = L * ‖y‖ ^ 2) :
    A.adjoint (A y) = (L : ℂ) • y := by
  by_cases hy : y = 0
  · simp [hy]
  let T := (A.adjoint.comp A).toContinuousLinearMap
  have hT : IsSelfAdjoint T :=
    (LinearMap.isSelfAdjoint_toContinuousLinearMap_iff _).2
      ((LinearMap.isSymmetric_iff_isSelfAdjoint _).mp A.isSymmetric_adjoint_comp_self)
  have hi (z : E) : T.reApplyInnerSelf z = ‖A z‖ ^ 2 := by
    change (inner ℂ (A.adjoint (A z)) z).re = ‖A z‖ ^ 2
    rw [A.adjoint_inner_left]
    simp [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow]
  have hm : IsMinOn T.reApplyInnerSelf (Metric.sphere 0 ‖y‖) y := by
    intro z hz
    have hzn : ‖z‖ = ‖y‖ := by simpa using hz
    change T.reApplyInnerSelf y ≤ T.reApplyInnerSelf z
    rw [hi, hi, heq, ← hzn]
    exact hbound z
  have hq : T.rayleighQuotient y = L := by
    rw [ContinuousLinearMap.rayleighQuotient, hi, heq]
    exact mul_div_cancel_right₀ L (pow_ne_zero 2 (norm_ne_zero_iff.mpr hy))
  have hh := hT.eq_smul_self_of_isLocalExtrOn (Or.inl hm.isLocalMinOn)
  rw [hq] at hh
  exact hh

/-- Norm equality is equivalent to membership in the bottom singular subspace. -/
theorem norm_attainment_iff_gram (A : E →ₗ[ℂ] F) {b : ℝ} (hb : 0 ≤ b)
    (hbound : ∀ z, b * ‖z‖ ≤ ‖A z‖) (y : E) :
    ‖A y‖ = b * ‖y‖ ↔ A.adjoint (A y) = ((b ^ 2 : ℝ) : ℂ) • y := by
  constructor
  · intro hy
    apply gram_eq_of_norm_attainment A
    · intro z
      have hh := hbound z
      have hn := mul_nonneg hb (norm_nonneg z)
      nlinarith [norm_nonneg (A z)]
    · rw [hy]
      ring
  · intro hy
    have hi := congrArg Complex.re (A.adjoint_inner_right y (A y))
    rw [hy] at hi
    simp only [inner_smul_right, inner_self_eq_norm_sq_to_K,
      Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im] at hi
    norm_num [RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_pow] at hi
    have hn := mul_nonneg hb (norm_nonneg y)
    nlinarith [norm_nonneg (A y)]

end ChiralGap
