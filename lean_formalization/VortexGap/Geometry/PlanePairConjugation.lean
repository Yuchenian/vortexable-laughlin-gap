import VortexGap.Physical.PlaneWeightedPair
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory

theorem planeTwoFramePair_conj (z : ℂ) :
    countableTwoFramePair (planeTwoFrame ((starRingEnd ℂ) z)) =
      star (countableTwoFramePair (planeTwoFrame z)) := by
  ext a
  simp [lp.star_apply, planeTwoFramePair_coefficient, ← Complex.exp_conj]

theorem countablePair_inner_star (p q : CountablePairSpace) :
    inner ℂ (star p) (star q) = star (inner ℂ p q) := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum, tsum_star]
  apply tsum_congr
  intro a
  simp [lp.star_apply, RCLike.inner_apply, mul_comm]

theorem planePair_coefficient_conj (q : CountablePairSpace) (z : ℂ) :
    ‖inner ℂ (countableTwoFramePair (planeTwoFrame ((starRingEnd ℂ) z))) (star q)‖ =
      ‖inner ℂ (countableTwoFramePair (planeTwoFrame z)) q‖ := by
  rw [planeTwoFramePair_conj, countablePair_inner_star, norm_star]

theorem planePairMeasure_integral_conj (F : ℂ → ℝ) :
    (∫ z, F ((starRingEnd ℂ) z) ∂planePairMeasure) = ∫ z, F z ∂planePairMeasure := by
  rw [planePairMeasure, integral_smul_measure, integral_smul_measure, plane_integral_conj]

theorem planePairOperator_energy_star (q : CountablePairSpace) :
    (inner ℂ (star q) (planePairOperator (star q))).re = (inner ℂ q (planePairOperator q)).re := by
  simp only [planePairOperator, countableContinuousPairOperator_energy]
  rw [← planePairMeasure_integral_conj (fun z => ‖inner ℂ (countableTwoFramePair (planeTwoFrame z)) (star q)‖^2)]
  simp only [planePair_coefficient_conj]

end VortexGap.Fermion
