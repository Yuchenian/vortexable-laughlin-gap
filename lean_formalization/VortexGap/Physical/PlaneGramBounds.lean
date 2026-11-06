import VortexGap.Physical.PlaneMultiplication
import VortexGap.Physical.PlaneWeightedBounds
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory
open scoped ComplexOrder BoundedContinuousFunction

theorem planeScalarGram_weight_integrable (ell : ℝ) (hell : 0 < ell) (f : ℂ →ᵇ ℂ)
    (v : CountableOrbital) :
    Integrable (fun z => ‖f z‖^2*‖inner ℂ (planeEvaluation ell z) v‖^2) := by
  have h := planeScalar_coefficient_memLp ell hell f v
  simpa only [norm_mul, mul_pow] using (memLp_two_iff_integrable_sq_norm h.aestronglyMeasurable).mp h

theorem planeScalarGram_pointwise_energy_bounds (ell : ℝ) (hell : 0 < ell) (f : ℂ →ᵇ ℂ)
    (g u : ℝ) (hw : ∀ z, g ≤ ‖f z‖^2 ∧ ‖f z‖^2 ≤ u) (v : CountableOrbital) :
    g*‖v‖^2 ≤ (inner ℂ v (planeScalarGram ell hell f v)).re ∧
      (inner ℂ v (planeScalarGram ell hell f v)).re ≤ u*‖v‖^2 := by
  rw [planeScalarGram_energy, ← planeEvaluation_integral_norm_sq ell hell v]
  have he := planeEvaluation_coefficient_memLp ell hell v
  have hi := (memLp_two_iff_integrable_sq_norm he.aestronglyMeasurable).mp he
  have hwI := planeScalarGram_weight_integrable ell hell f v
  constructor
  · rw [← integral_const_mul]
    apply integral_mono (hi.const_mul g) hwI
    intro z
    exact mul_le_mul_of_nonneg_right (hw z).1 (sq_nonneg _)
  · rw [← integral_const_mul]
    apply integral_mono hwI (hi.const_mul u)
    intro z
    exact mul_le_mul_of_nonneg_right (hw z).2 (sq_nonneg _)

theorem planeScalarGram_pointwise_bounds (ell : ℝ) (hell : 0 < ell) (f : ℂ →ᵇ ℂ)
    (g u : ℝ) (hg : 0 ≤ g) (hu : 0 ≤ u)
    (hw : ∀ z, g ≤ ‖f z‖^2 ∧ ‖f z‖^2 ≤ u) :
    g • (1 : CountableOrbital →L[ℂ] CountableOrbital) ≤ planeScalarGram ell hell f ∧
      planeScalarGram ell hell f ≤ u • (1 : CountableOrbital →L[ℂ] CountableOrbital) := by
  have hG : (planeScalarGram ell hell f).IsPositive :=
    ContinuousLinearMap.nonneg_iff_isPositive.mp (gramOperator_nonneg _)
  have hp (c : ℝ) (hc : 0 ≤ c) : (c • (1 : CountableOrbital →L[ℂ] CountableOrbital)).IsPositive := by
    have he : c • (1 : CountableOrbital →L[ℂ] CountableOrbital) = (c : ℂ) • 1 := by
      ext v
      rfl
    rw [he]
    exact ContinuousLinearMap.nonneg_iff_isPositive.mp
      (smul_nonneg (show 0 ≤ (c : ℂ) by exact_mod_cast hc) zero_le_one)
  have he (c : ℝ) (v : CountableOrbital) :
      (inner ℂ v ((c • (1 : CountableOrbital →L[ℂ] CountableOrbital)) v)).re = c*‖v‖^2 := by
    change (inner ℂ v ((c : ℂ) • v)).re = _
    rw [inner_smul_right, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    congr 1
    simpa only [RCLike.re_eq_complex_re] using! (norm_sq_eq_re_inner (𝕜 := ℂ) v).symm
  constructor
  · apply positive_operator_le_of_energy _ _ (hp g hg) hG
    intro v
    rw [he]
    exact (planeScalarGram_pointwise_energy_bounds ell hell f g u hw v).1
  · apply positive_operator_le_of_energy _ _ hG (hp u hu)
    intro v
    rw [he]
    exact (planeScalarGram_pointwise_energy_bounds ell hell f g u hw v).2

end VortexGap.Fermion
