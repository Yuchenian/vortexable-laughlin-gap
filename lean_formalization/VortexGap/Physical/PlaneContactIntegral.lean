import VortexGap.Geometry.PlaneContactCoordinates
import VortexGap.Geometry.PlaneMeasurability
import VortexGap.Frame.CountableFilteredPair
import Mathlib.Topology.ContinuousMap.Bounded.Normed
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory Filter VortexGap.Frame
open scoped ComplexOrder BoundedContinuousFunction

theorem planeFilteredPair_bessel_bound (D : CountablePairSpace →L[ℂ] CountablePairSpace)
    (q : CountablePairSpace) :
    (∫ a, ‖inner ℂ (D (countableTwoFramePair (planeTwoFrame a))) q‖^2 ∂planePairMeasure) ≤
      ‖D‖^2*‖q‖^2 := by
  simp_rw [← ContinuousLinearMap.adjoint_inner_right]
  apply (planePair_bessel (D.adjoint q)).trans
  have h := D.adjoint.le_opNorm q
  rw [ContinuousLinearMap.adjoint.norm_map] at h
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) h 2

theorem planeFilteredPair_apply_memLp (D : CountablePairSpace →L[ℂ] CountablePairSpace)
    (N : ℕ) (x : countableSector N) :
    MemLp (fun a => countablePairAnnihilate N (D (countableTwoFramePair (planeTwoFrame a))) x)
      2 planePairMeasure := by
  exact countableFrameApply_memLp planePairMeasure _
    (countableFilteredPair_coeff_memLp planePairMeasure _ planePair_coefficient_memLp D)
    (‖D‖^2) (sq_nonneg _) (planeFilteredPair_bessel_bound D)
    (spanningSets planePairMeasure)
    (increasingCutoffs_aecover planePairMeasure (spanningSets planePairMeasure)
      (measurableSet_spanningSets planePairMeasure) (monotone_spanningSets planePairMeasure)
      (iUnion_spanningSets planePairMeasure))
    (fun n => countableFilteredPair_local_memLp planePairMeasure _ D _
      (planeTwoFramePair_spanning_memLp n)) N x

theorem planeContact_weighted_pair_integrable
    (D : CountablePairSpace →L[ℂ] CountablePairSpace) (ell : ℝ) (f : ℂ →ᵇ ℂ)
    (N : ℕ) (x : countableSector N) :
    Integrable (fun a => ‖f ((Real.sqrt 2*ell : ℝ) • (starRingEnd ℂ) a)‖^4 *
      ‖countablePairAnnihilate N (D (countableTwoFramePair (planeTwoFrame a))) x‖^2)
      planePairMeasure := by
  have hm := planeFilteredPair_apply_memLp D N x
  have hi := (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm
  apply hi.bdd_mul (c := ‖f‖^4)
  · have hc : Continuous (fun a : ℂ => (Real.sqrt 2*ell : ℝ) • (starRingEnd ℂ) a) :=
      (continuous_const : Continuous (fun _ : ℂ => (Real.sqrt 2*ell : ℝ))).smul
        Complex.continuous_conj
    have hw : Continuous (fun a : ℂ => ‖f ((Real.sqrt 2*ell : ℝ) • (starRingEnd ℂ) a)‖^4) :=
      (f.continuous.comp hc).norm.pow 4
    exact hw.aestronglyMeasurable
  · apply Eventually.of_forall
    intro a
    change ‖‖f ((Real.sqrt 2*ell : ℝ) • (starRingEnd ℂ) a)‖^4‖ ≤ ‖f‖^4
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (f.norm_coe_le_norm _) 4

/-- Integral of the independently defined physical derivative-contact density. -/
def planeScalarContactEnergy (R : CountableOrbital →L[ℂ] CountableOrbital)
    (ell : ℝ) (f : ℂ → ℂ) (N : ℕ) (x : countableSector N) : ℝ :=
  ∫ z : ℂ, planeScalarContactDensity R ell f z N x

theorem planeScalarContactEnergy_pair (R : CountableOrbital →L[ℂ] CountableOrbital)
    (hR : 0 ≤ R) (ell : ℝ) (hell : 0 < ell) (f : ℂ → ℂ)
    (hf : Differentiable ℝ f) (N : ℕ) (x : countableSector N) :
    planeScalarContactEnergy R ell f N x =
      ∫ a, ‖f ((Real.sqrt 2*ell : ℝ) • (starRingEnd ℂ) a)‖^4 *
        ‖countablePairAnnihilate N (countablePairFilter R hR
          (countableTwoFramePair (planeTwoFrame a))) x‖^2 ∂planePairMeasure := by
  unfold planeScalarContactEnergy
  simp_rw [planeScalarContactDensity_pair R hR ell hell f _ (hf _) N x]
  exact planeContact_integral_weight ell hell (fun z => ‖f z‖^4)
    (fun a => ‖countablePairAnnihilate N (countablePairFilter R hR
      (countableTwoFramePair (planeTwoFrame a))) x‖^2)

theorem planeScalarContactDensity_integrable (R : CountableOrbital →L[ℂ] CountableOrbital)
    (hR : 0 ≤ R) (ell : ℝ) (hell : 0 < ell) (f : ℂ →ᵇ ℂ)
    (hf : Differentiable ℝ f) (N : ℕ) (x : countableSector N) :
    Integrable (fun z => planeScalarContactDensity R ell f z N x) := by
  have hi := (planeContact_integrable_coordinates_iff ell hell _).mpr
    (planeContact_weighted_pair_integrable (countablePairFilter R hR) ell f N x)
  simp_rw [planeContact_inverse_coordinate ell hell] at hi
  have hj := hi.const_mul (1/(Real.pi*ell^2))
  convert hj using 1
  funext z
  rw [planeScalarContactDensity_pair R hR ell hell f z (hf z) N x]
  ring

end VortexGap.Fermion
