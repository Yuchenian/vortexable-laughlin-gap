import VortexGap.Fermion.FiniteLoss

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped BigOperators InnerProduct ComplexConjugate ComplexOrder

/-- Projection back from a genuine finite Hilbert isometry is contractive. -/
theorem euclideanIsometry_adjoint_norm_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (U : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ κ) (y : EuclideanSpace ℂ κ) :
    ‖U.toLinearMap.adjoint y‖ ≤ ‖y‖ := by
  have h : ‖U.toLinearMap.adjoint y‖ ^ 2 ≤ ‖U.toLinearMap.adjoint y‖ * ‖y‖ := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), LinearMap.adjoint_inner_right]
    calc
      _ ≤ ‖U (U.toLinearMap.adjoint y)‖ * ‖y‖ := re_inner_le_norm (𝕜 := ℂ) _ _
      _ = _ := by rw [U.norm_map]
  by_cases hz : ‖U.toLinearMap.adjoint y‖ = 0
  · rw [hz]; exact norm_nonneg y
  · have hp : 0 < ‖U.toLinearMap.adjoint y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    nlinarith only [h, hp]

theorem orbitalSys_env_inner {n m : ℕ} (u : EuclideanSpace ℂ (Fin m)) (v : EuclideanSpace ℂ (Fin n)) :
    inner ℂ (orbitalSys n m u) (orbitalEnv n m v) = 0 := by
  rw [PiLp.inner_apply, Fin.sum_univ_add]
  simp only [orbitalSys_left, orbitalSys_right, orbitalEnv_left, orbitalEnv_right,
    inner_zero_left, inner_zero_right, Finset.sum_const_zero, add_zero]

theorem orbitalSys_adjoint_lossEmbedding {n : ℕ}
    (M : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1) :
    (orbitalSys n n).toLinearMap.adjoint.comp (finiteLossEmbedding M hM hc).toLinearMap = M.toLinearMap := by
  apply LinearMap.ext
  intro v
  apply ext_inner_left ℂ
  intro u
  change inner ℂ u ((orbitalSys n n).toLinearMap.adjoint (finiteLossEmbedding M hM hc v)) = inner ℂ u (M v)
  rw [LinearMap.adjoint_inner_right]
  change inner ℂ (orbitalSys n n u) (finiteLossEmbedding M hM hc v) = _
  rw [finiteLossEmbedding_apply, inner_add_right, orbitalSys_env_inner,
    (orbitalSys n n).inner_map_map, zero_add]

/-- Contractivity of the exterior square follows from the concrete dilation and projection. -/
theorem exteriorSquare_positive_contraction_norm_le {n : ℕ}
    (M : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1)
    (p : PairSpace n) : ‖exteriorSquare M.toLinearMap p‖ ≤ ‖p‖ := by
  have he : exteriorSquare M.toLinearMap p =
      (exteriorSquareIsometry (orbitalSys n n)).toLinearMap.adjoint
        (exteriorSquareIsometry (finiteLossEmbedding M hM hc) p) := by
    change exteriorSquare M.toLinearMap p =
      (exteriorSquare (orbitalSys n n).toLinearMap).adjoint
        (exteriorSquare (finiteLossEmbedding M hM hc).toLinearMap p)
    rw [← exteriorSquare_adjoint, ← LinearMap.comp_apply, ← exteriorSquare_comp,
      orbitalSys_adjoint_lossEmbedding]
  rw [he]
  calc
    _ ≤ ‖exteriorSquareIsometry (finiteLossEmbedding M hM hc) p‖ :=
      euclideanIsometry_adjoint_norm_le (exteriorSquareIsometry (orbitalSys n n)) _
    _ = _ := (exteriorSquareIsometry (finiteLossEmbedding M hM hc)).norm_map p

theorem exteriorSquare_smul {n m : ℕ} (z : ℂ)
    (A : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m)) :
    exteriorSquare (z • A) = z ^ 2 • exteriorSquare A := by
  have hb (a : PairIndex n) : exteriorSquare (z • A) (pairBasis a) = z ^ 2 • exteriorSquare A (pairBasis a) := by
    rw [exteriorSquare_pairBasis, exteriorSquare_pairBasis]
    ext b
    simp only [LinearMap.smul_apply, wedgePair, PiLp.toLp_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  apply LinearMap.ext
  intro p
  conv_lhs => rw [← pairBasis_expansion p]
  conv_rhs => rw [← pairBasis_expansion p]
  simp only [map_sum, map_smul, LinearMap.smul_apply]
  exact Finset.sum_congr rfl fun a _ => by rw [hb, smul_comm]

theorem exteriorSquare_zero (n m : ℕ) :
    exteriorSquare (0 : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m)) = 0 := by
  simpa using exteriorSquare_smul (0 : ℂ) (0 : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m))

/-- General positive operators are rescaled to the already constructed contraction dilation. -/
theorem exteriorSquare_positive_norm_le {n : ℕ}
    (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) (hA : 0 ≤ A) (p : PairSpace n) :
    ‖exteriorSquare A.toLinearMap p‖ ≤ ‖A‖ ^ 2 * ‖p‖ := by
  by_cases hz : ‖A‖ = 0
  · have hA0 : A = 0 := norm_eq_zero.mp hz
    subst A
    simp [exteriorSquare_zero]
  · let S : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) := ((‖A‖⁻¹ : ℝ) : ℂ) • A
    have hzC : (0 : ℂ) ≤ ((‖A‖⁻¹ : ℝ) : ℂ) := by
      rw [Complex.le_def]
      exact ⟨inv_nonneg.mpr (norm_nonneg A), rfl⟩
    have hS : 0 ≤ S := smul_nonneg hzC hA
    have hc : ‖S‖ ≤ 1 := by
      simp only [S, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr (norm_nonneg A)), inv_mul_cancel₀ hz, le_refl]
    have he : (‖A‖ : ℂ) • S = A := by
      dsimp [S]
      rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hz, Complex.ofReal_one, one_smul]
    have heL : (‖A‖ : ℂ) • S.toLinearMap = A.toLinearMap := congrArg ContinuousLinearMap.toLinearMap he
    rw [← heL, exteriorSquare_smul, LinearMap.smul_apply, norm_smul, norm_pow,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg A)]
    exact mul_le_mul_of_nonneg_left (exteriorSquare_positive_contraction_norm_le S hS hc p) (sq_nonneg _)

theorem exteriorSquare_positive_opNorm_le {n : ℕ}
    (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) (hA : 0 ≤ A) :
    ‖(exteriorSquare A.toLinearMap).toContinuousLinearMap‖ ≤ ‖A‖ ^ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (sq_nonneg _)
  exact exteriorSquare_positive_norm_le A hA

theorem lossDefect_exteriorSquare_norm_le {n : ℕ}
    (M : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1) :
    ‖(exteriorSquare (lossDefect M).toLinearMap).toContinuousLinearMap‖ ≤ ‖1 - M ^ 2‖ := by
  have h := exteriorSquare_positive_opNorm_le (lossDefect M) (lossDefect_nonneg M)
  rw [lossDefect_norm_sq M hM hc] at h
  exact h

end VortexGap.Fermion
