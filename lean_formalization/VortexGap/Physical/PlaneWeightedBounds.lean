import VortexGap.Physical.PlaneWeightedPair
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory
open scoped ComplexOrder BoundedContinuousFunction

theorem positive_operator_le_of_energy {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A B : H →L[ℂ] H) (hA : A.IsPositive) (hB : B.IsPositive)
    (h : ∀ x, (inner ℂ x (A x)).re ≤ (inner ℂ x (B x)).re) : A ≤ B := by
  apply ContinuousLinearMap.le_def.mpr
  refine ⟨hB.isSymmetric.sub hA.isSymmetric, ?_⟩
  intro x
  change 0 ≤ (inner ℂ ((B-A) x) x).re
  have he : (inner ℂ ((B-A) x) x).re = (inner ℂ x ((B-A) x)).re := by
    simpa only [RCLike.re_eq_complex_re] using! (inner_re_symm (𝕜 := ℂ) ((B-A) x) x)
  rw [he]
  simpa only [sub_apply, inner_sub_right, Complex.sub_re, sub_nonneg] using h x

theorem planeWeightedPairOperator_upper (ell : ℝ) (f : ℂ →ᵇ ℂ) :
    planeWeightedPairOperator ell f ≤ (‖f‖^4 : ℂ) • planePairOperator := by
  have hQ : 0 ≤ planePairOperator :=
    ContinuousLinearMap.nonneg_iff_isPositive.mpr planePairOperator_positive
  apply positive_operator_le_of_energy _ _ (planeWeightedPairOperator_positive ell f)
    (ContinuousLinearMap.nonneg_iff_isPositive.mp (smul_nonneg
      (show 0 ≤ (‖f‖^4 : ℂ) by exact_mod_cast (show 0 ≤ ‖f‖^4 by positivity)) hQ))
  intro q
  simp only [← Complex.ofReal_pow, smul_apply, inner_smul_right, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  rw [planeWeightedPairOperator, planePairOperator, countableContinuousPairOperator_energy,
    countableContinuousPairOperator_energy]
  exact planeWeightedPair_integral_bound ell f q

/-- Pointwise lower contact weight gives a sufficient coercivity bound. The final
criterion may instead supply a sharper projected bound, allowing nodal f. -/
theorem planeWeightedPairOperator_lower (ell : ℝ) (f : ℂ →ᵇ ℂ) (κ : ℝ) (hκ : 0 ≤ κ)
    (hw : ∀ z, κ ≤ ‖f z‖^4) :
    (κ : ℂ) • planePairOperator ≤ planeWeightedPairOperator ell f := by
  have hQ : 0 ≤ planePairOperator :=
    ContinuousLinearMap.nonneg_iff_isPositive.mpr planePairOperator_positive
  apply positive_operator_le_of_energy _ _
    (ContinuousLinearMap.nonneg_iff_isPositive.mp (smul_nonneg
      (show 0 ≤ (κ : ℂ) by exact_mod_cast hκ) hQ)) (planeWeightedPairOperator_positive ell f)
  intro q
  simp only [smul_apply, inner_smul_right, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  rw [planeWeightedPairOperator, planePairOperator, countableContinuousPairOperator_energy,
    countableContinuousPairOperator_energy, ← integral_const_mul]
  have hp := planePair_coefficient_memLp q
  have hwp := planeWeightedPair_coefficient_memLp ell f q
  apply integral_mono
    (((memLp_two_iff_integrable_sq_norm hp.aestronglyMeasurable).mp hp).const_mul κ)
    ((memLp_two_iff_integrable_sq_norm hwp.aestronglyMeasurable).mp hwp)
  intro a
  change κ*‖inner ℂ (countableTwoFramePair (planeTwoFrame a)) q‖^2 ≤
    ‖inner ℂ (planeWeightedPair ell f a) q‖^2
  rw [planeWeightedPair_coefficient_norm, mul_pow, planeContactWeightRoot_norm, ← pow_mul]
  exact mul_le_mul_of_nonneg_right (hw _) (sq_nonneg _)

end VortexGap.Fermion
