import VortexGap.Physical.PlaneContactIntegral
import VortexGap.Geometry.PlaneResolution
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory Filter
open scoped ComplexOrder BoundedContinuousFunction

/-- Square-root contact weight in the actual coherent-pair coordinate convention. -/
def planeContactWeightRoot (ell : ℝ) (f : ℂ →ᵇ ℂ) (a : ℂ) : ℂ :=
  (‖f ((Real.sqrt 2*ell : ℝ) • (starRingEnd ℂ) a)‖^2 : ℝ)

theorem planeContactWeightRoot_continuous (ell : ℝ) (f : ℂ →ᵇ ℂ) :
    Continuous (planeContactWeightRoot ell f) := by
  have hc : Continuous (fun a : ℂ => (Real.sqrt 2*ell : ℝ) • (starRingEnd ℂ) a) :=
    (continuous_const : Continuous (fun _ : ℂ => (Real.sqrt 2*ell : ℝ))).smul
      Complex.continuous_conj
  exact Complex.continuous_ofReal.comp ((f.continuous.comp hc).norm.pow 2)

theorem planeContactWeightRoot_norm (ell : ℝ) (f : ℂ →ᵇ ℂ) (a : ℂ) :
    ‖planeContactWeightRoot ell f a‖ = ‖f ((Real.sqrt 2*ell : ℝ) • (starRingEnd ℂ) a)‖^2 := by
  simp [planeContactWeightRoot, Complex.norm_real]

theorem planeContactWeightRoot_bound (ell : ℝ) (f : ℂ →ᵇ ℂ) (a : ℂ) :
    ‖planeContactWeightRoot ell f a‖ ≤ ‖f‖^2 := by
  rw [planeContactWeightRoot_norm]
  exact pow_le_pow_left₀ (norm_nonneg _) (f.norm_coe_le_norm _) 2

/-- Actual weighted pair vectors; zeros of f are permitted. -/
def planeWeightedPair (ell : ℝ) (f : ℂ →ᵇ ℂ) (a : ℂ) : CountablePairSpace :=
  planeContactWeightRoot ell f a • countableTwoFramePair (planeTwoFrame a)

theorem planeWeightedPair_coefficient_norm (ell : ℝ) (f : ℂ →ᵇ ℂ)
    (a : ℂ) (q : CountablePairSpace) :
    ‖inner ℂ (planeWeightedPair ell f a) q‖ =
      ‖planeContactWeightRoot ell f a‖ * ‖inner ℂ (countableTwoFramePair (planeTwoFrame a)) q‖ := by
  simp [planeWeightedPair, mul_comm]

theorem planeWeightedPair_coefficient_memLp (ell : ℝ) (f : ℂ →ᵇ ℂ) (q : CountablePairSpace) :
    MemLp (fun a => inner ℂ (planeWeightedPair ell f a) q) 2 planePairMeasure := by
  apply (planePair_coefficient_memLp q).of_le_mul (c := ‖f‖^2)
  · simp only [planeWeightedPair, inner_smul_left]
    exact ((Complex.continuous_conj.comp (planeContactWeightRoot_continuous ell f)).aestronglyMeasurable).mul
      (planePair_coefficient_memLp q).aestronglyMeasurable
  · exact Eventually.of_forall (fun a => by
      rw [planeWeightedPair_coefficient_norm]
      exact mul_le_mul_of_nonneg_right (planeContactWeightRoot_bound ell f a) (norm_nonneg _))

theorem planeWeightedPair_integral_bound (ell : ℝ) (f : ℂ →ᵇ ℂ) (q : CountablePairSpace) :
    (∫ a, ‖inner ℂ (planeWeightedPair ell f a) q‖^2 ∂planePairMeasure) ≤
      ‖f‖^4 * ∫ a, ‖inner ℂ (countableTwoFramePair (planeTwoFrame a)) q‖^2 ∂planePairMeasure := by
  have hm := planeWeightedPair_coefficient_memLp ell f q
  have hn := planePair_coefficient_memLp q
  rw [← integral_const_mul]
  apply integral_mono ((memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm)
    (((memLp_two_iff_integrable_sq_norm hn.aestronglyMeasurable).mp hn).const_mul _)
  intro a
  change ‖inner ℂ (planeWeightedPair ell f a) q‖^2 ≤
    ‖f‖^4*‖inner ℂ (countableTwoFramePair (planeTwoFrame a)) q‖^2
  rw [planeWeightedPair_coefficient_norm, mul_pow]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  simpa only [← pow_mul] using pow_le_pow_left₀ (norm_nonneg _)
    (planeContactWeightRoot_bound ell f a) 2

theorem planeWeightedPair_bessel (ell : ℝ) (f : ℂ →ᵇ ℂ) (q : CountablePairSpace) :
    (∫ a, ‖inner ℂ (planeWeightedPair ell f a) q‖^2 ∂planePairMeasure) ≤ ‖f‖^4*‖q‖^2 :=
  (planeWeightedPair_integral_bound ell f q).trans
    (mul_le_mul_of_nonneg_left (planePair_bessel q) (by positivity))

theorem planeWeightedPair_spanning_memLp (ell : ℝ) (f : ℂ →ᵇ ℂ) (n : ℕ) :
    MemLp (planeWeightedPair ell f) 2
      (planePairMeasure.restrict (spanningSets planePairMeasure n)) := by
  have hp := planeTwoFramePair_spanning_memLp n
  apply hp.of_le_mul (c := ‖f‖^2)
  · exact (planeContactWeightRoot_continuous ell f).aestronglyMeasurable.smul hp.aestronglyMeasurable
  · exact Eventually.of_forall (fun a => by
      change ‖planeContactWeightRoot ell f a • countableTwoFramePair (planeTwoFrame a)‖ ≤ _
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (planeContactWeightRoot_bound ell f a) (norm_nonneg _))

/-- Weak integral of the actual |f|^4-weighted coherent pairs. -/
def planeWeightedPairOperator (ell : ℝ) (f : ℂ →ᵇ ℂ) : CountablePairSpace →L[ℂ] CountablePairSpace :=
  countableContinuousPairOperator planePairMeasure (planeWeightedPair ell f)
    (planeWeightedPair_coefficient_memLp ell f) (‖f‖^4) (by positivity) (planeWeightedPair_bessel ell f)

theorem planeWeightedPairOperator_positive (ell : ℝ) (f : ℂ →ᵇ ℂ) :
    (planeWeightedPairOperator ell f).IsPositive :=
  countableContinuousPairOperator_positive _ _ _ _ _ _

theorem planeWeightedPairOperator_energy (ell : ℝ) (f : ℂ →ᵇ ℂ) (q : CountablePairSpace) :
    (inner ℂ q (planeWeightedPairOperator ell f q)).re =
      ∫ a, ‖f ((Real.sqrt 2*ell : ℝ) • (starRingEnd ℂ) a)‖^4 *
        ‖inner ℂ (countableTwoFramePair (planeTwoFrame a)) q‖^2 ∂planePairMeasure := by
  rw [planeWeightedPairOperator, countableContinuousPairOperator_energy]
  simp only [planeWeightedPair_coefficient_norm, mul_pow, planeContactWeightRoot_norm, ← pow_mul]

end VortexGap.Fermion
