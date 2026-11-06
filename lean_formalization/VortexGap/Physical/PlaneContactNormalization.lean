import VortexGap.Physical.PlaneContactOperator
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory Filter VortexGap.Frame
open scoped ComplexOrder

theorem planeContact_identity_filter :
    countablePairFilter 1 (show (0 : CountableOrbital →L[ℂ] CountableOrbital) ≤ 1 from zero_le_one) = 1 := by
  apply countablePairOperator_ext_wedge
  intro u v
  simp only [countablePairFilter_wedge, one_apply_eq_self]

/-- Calibration of the independently differentiated and integrated contact,
for any constant complex multiplier and every finite particle number. -/
theorem planeScalarContactEnergy_constant (ell : ℝ) (hell : 0 < ell) (c : ℂ)
    (N : ℕ) (x : countableSector N) :
    planeScalarContactEnergy 1 ell (fun _ => c) N x =
      ‖c‖^4*(inner ℂ x (countablePairLift N planePairOperator x)).re := by
  rw [planeScalarContactEnergy_pair 1 (show (0 : CountableOrbital →L[ℂ] CountableOrbital) ≤ 1 from zero_le_one)
    ell hell _ (differentiable_const c) N x]
  simp only [planeContact_identity_filter, one_apply_eq_self]
  rw [integral_const_mul]
  congr 1
  exact (countableContinuousFrame_energy planePairMeasure
    (fun a => countableTwoFramePair (planeTwoFrame a)) planePair_coefficient_memLp
    1 (by norm_num) (fun q => by simpa only [one_mul] using planePair_bessel q)
    (spanningSets planePairMeasure)
    (increasingCutoffs_aecover planePairMeasure (spanningSets planePairMeasure)
      (measurableSet_spanningSets planePairMeasure) (monotone_spanningSets planePairMeasure)
      (iUnion_spanningSets planePairMeasure))
    planeTwoFramePair_spanning_memLp (monotone_spanningSets planePairMeasure)
    (iUnion_spanningSets planePairMeasure) N x).symm

/-- The K=3 pair mixes the (0,3) and (1,2) occupations. -/
def planeContactBlockTest : countableSector 2 :=
  ⟨countablePairEmbedding (planeBlockVector 3), countablePairEmbedding_sector _⟩

theorem planeContactBlockTest_norm_sq : ‖planeContactBlockTest‖^2 = 1 := by
  change ‖countablePairEmbedding (planeBlockVector 3)‖^2 = 1
  rw [countablePairEmbedding.norm_map]
  exact planeBlockVector_norm_sq 3 (by norm_num)

theorem planeContactBlockTest_reference_energy :
    (inner ℂ planeContactBlockTest (countablePairLift 2 planePairOperator planeContactBlockTest)).re = 1 := by
  have hq : planePairOperator (planeBlockVector 3) = planeBlockVector 3 := by
    have h := planePairOperator_on_block_span (lp.single 2 2 1)
    simpa only [planeBlockSynthesis_single] using h
  have he : countablePairLift 2 planePairOperator planeContactBlockTest = planeContactBlockTest := by
    simp only [planeContactBlockTest, countablePairLift_pairEmbedding, hq]
  rw [he]
  calc
    _ = ‖planeContactBlockTest‖^2 := by
      simpa only [RCLike.re_eq_complex_re] using!
        (norm_sq_eq_re_inner (𝕜 := ℂ) planeContactBlockTest).symm
    _ = 1 := planeContactBlockTest_norm_sq

/-- Nonzero integrated physical contact with a complex amplitude and a mixed pair.
This tests normalization and the fourth power; it is not a reference-gap input. -/
theorem planeContactBlockTest_complex_energy (ell : ℝ) (hell : 0 < ell) :
    planeScalarContactEnergy 1 ell (fun _ => 1+Complex.I) 2 planeContactBlockTest = 4 := by
  rw [planeScalarContactEnergy_constant ell hell, planeContactBlockTest_reference_energy, mul_one]
  have hn : ‖(1 : ℂ)+Complex.I‖^2 = 2 := by
    rw [Complex.sq_norm]
    norm_num [Complex.normSq_apply]
  nlinarith [sq_nonneg (‖(1 : ℂ)+Complex.I‖^2-2)]

end VortexGap.Fermion
