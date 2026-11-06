import VortexGap.Geometry.PlanePositionSynthesis
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory
open scoped ENNReal

/-- Conjugate angular coordinates used for the right-slot frame coefficient. -/
def planePairRightCoordinates (q : CountablePairSpace) : CountableOrbital :=
  ⟨fun n => inner ℂ q (planeBlockVector (n+1)), by
    apply memℓp_gen
    simp only [show (2 : ℝ≥0∞).toReal = (2 : ℝ) by norm_num, Real.rpow_two]
    simpa only [norm_inner_symm q] using planeBlockVector_orthonormal.inner_products_summable q⟩

theorem planePairRightCoordinates_norm_sq_le (q : CountablePairSpace) :
    ‖planePairRightCoordinates q‖^2 ≤ ‖q‖^2 := by
  have hn : ‖planePairRightCoordinates q‖^2 =
      ∑' n, ‖inner ℂ q (planeBlockVector (n+1))‖^2 := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, planePairRightCoordinates] using
      lp.norm_rpow_eq_tsum (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)
        (planePairRightCoordinates q)
  rw [hn]
  simpa only [norm_inner_symm q] using planeBlockVector_orthonormal.tsum_inner_products_le q

theorem planePair_right_coefficient_series (q : CountablePairSpace) (z : ℂ) :
    inner ℂ q (countableTwoFramePair (planeTwoFrame z)) =
      ∑' n, planePairRightCoordinates q n * planePairAmplitude z (n+1) := by
  have hs := (planeTwoFramePair_hasSum_blocks z).map
    (innerSL ℂ q).toAddMonoidHom (innerSL ℂ q).continuous
  have hs' : HasSum (fun n => planePairRightCoordinates q n * planePairAmplitude z (n+1))
      (inner ℂ q (countableTwoFramePair (planeTwoFrame z))) := by
    change HasSum (fun n => inner ℂ q (planePairAmplitude z (n+1) • planeBlockVector (n+1)))
      (inner ℂ q (countableTwoFramePair (planeTwoFrame z))) at hs
    simpa only [inner_smul_right, planePairRightCoordinates, mul_comm] using hs
  exact hs'.tsum_eq.symm

theorem planePair_right_coefficient_memLp (q : CountablePairSpace) :
    MemLp (fun z => inner ℂ q (countableTwoFramePair (planeTwoFrame z))) 2 planePairMeasure := by
  simp_rw [planePair_right_coefficient_series]
  exact planeAmplitude_series_memLp (planePairRightCoordinates q)

theorem planePair_right_coefficient_integral (q : CountablePairSpace) :
    (∫ z, ‖inner ℂ q (countableTwoFramePair (planeTwoFrame z))‖^2 ∂planePairMeasure) =
      ‖planePairRightCoordinates q‖^2 := by
  simp_rw [planePair_right_coefficient_series]
  exact planeAmplitude_series_integral (planePairRightCoordinates q)

theorem planePair_bessel (q : CountablePairSpace) :
    (∫ z, ‖inner ℂ (countableTwoFramePair (planeTwoFrame z)) q‖^2 ∂planePairMeasure) ≤ ‖q‖^2 := by
  simp_rw [norm_inner_symm (countableTwoFramePair (planeTwoFrame _)) q]
  rw [planePair_right_coefficient_integral]
  exact planePairRightCoordinates_norm_sq_le q

theorem planePair_coefficient_memLp (q : CountablePairSpace) :
    MemLp (fun z => inner ℂ (countableTwoFramePair (planeTwoFrame z)) q) 2 planePairMeasure := by
  have h := (planePair_right_coefficient_memLp q).star
  convert h using 1
  funext z
  exact (inner_conj_symm _ _).symm

theorem planePair_block_coefficient (m : ℕ) (z : ℂ) :
    inner ℂ (planeBlockVector (m+1)) (countableTwoFramePair (planeTwoFrame z)) =
      planePairAmplitude z (m+1) := by
  rw [planePair_right_coefficient_series]
  simp [planePairRightCoordinates, orthonormal_iff_ite.mp planeBlockVector_orthonormal]

/-- The bound is saturated on every normalized angular block, including the
nontrivial K=3 block with occupation weights 3/4 and 1/4. -/
theorem planePair_bessel_saturated (m : ℕ) :
    (∫ z, ‖inner ℂ (countableTwoFramePair (planeTwoFrame z))
      (planeBlockVector (m+1))‖^2 ∂planePairMeasure) = 1 := by
  simp_rw [norm_inner_symm (countableTwoFramePair (planeTwoFrame _)), planePair_block_coefficient]
  exact planePairAmplitude_integral m

end VortexGap.Fermion


