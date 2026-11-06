import VortexGap.Physical.PlaneContactDensity
import VortexGap.Geometry.PlanePhysicalScale
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory

theorem plane_integral_conj (F : ℂ → ℝ) :
    (∫ z : ℂ, F ((starRingEnd ℂ) z)) = ∫ z : ℂ, F z := by
  simpa only [Complex.conjLIE_apply] using
    Complex.conjLIE.measurePreserving.integral_comp
      Complex.conjLIE.toHomeomorph.measurableEmbedding F

theorem planeCoordinate_real_smul (ell : ℝ) (z : ℂ) :
    planeCoordinate ell z = (Real.sqrt 2*ell)⁻¹ • z := by
  simp [planeCoordinate, div_eq_mul_inv, mul_comm]

/-- The physical contact measure becomes the coherent-pair measure, including
the conjugation forced by the antilinear annihilation convention. -/
theorem planeContact_integral_coordinates (ell : ℝ) (hell : 0 < ell) (F : ℂ → ℝ) :
    (∫ z : ℂ, (1/(Real.pi*ell^2))*F ((starRingEnd ℂ) (planeCoordinate ell z))) =
      ∫ a, F a ∂planePairMeasure := by
  simp_rw [planeCoordinate_real_smul]
  rw [integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg volume
    (fun z : ℂ => F ((starRingEnd ℂ) z)) (show 0 ≤ Real.sqrt 2*ell by positivity),
    Complex.finrank_real_complex, smul_eq_mul, plane_integral_conj,
    planePairMeasure, integral_smul_measure, ENNReal.toReal_ofReal (by positivity),
    smul_eq_mul, mul_pow, Real.sq_sqrt (by norm_num)]
  field_simp

theorem planeContact_inverse_coordinate (ell : ℝ) (hell : 0 < ell) (z : ℂ) :
    (Real.sqrt 2*ell : ℝ) • (starRingEnd ℂ) ((starRingEnd ℂ) (planeCoordinate ell z)) = z := by
  rw [starRingEnd_self_apply, planeCoordinate_real_smul, smul_smul,
    mul_inv_cancel₀ (by positivity : Real.sqrt 2*ell ≠ 0), one_smul]

theorem planeContact_integral_weight (ell : ℝ) (hell : 0 < ell)
    (w F : ℂ → ℝ) :
    (∫ z : ℂ, w z*(1/(Real.pi*ell^2))*F ((starRingEnd ℂ) (planeCoordinate ell z))) =
      ∫ a, w ((Real.sqrt 2*ell : ℝ) • (starRingEnd ℂ) a)*F a ∂planePairMeasure := by
  have h := planeContact_integral_coordinates ell hell
    (fun a => w ((Real.sqrt 2*ell : ℝ) • (starRingEnd ℂ) a)*F a)
  simp_rw [planeContact_inverse_coordinate ell hell] at h
  convert h using 1
  congr 1
  funext z
  ring

theorem plane_integrable_conj_iff (F : ℂ → ℝ) :
    Integrable (fun z => F ((starRingEnd ℂ) z)) ↔ Integrable F := by
  simpa only [Function.comp_def, Complex.conjLIE_apply] using
    Complex.conjLIE.measurePreserving.integrable_comp_emb
      Complex.conjLIE.toHomeomorph.measurableEmbedding (g := F)

theorem planeContact_integrable_coordinates_iff (ell : ℝ) (hell : 0 < ell)
    (F : ℂ → ℝ) :
    Integrable (fun z => F ((starRingEnd ℂ) (planeCoordinate ell z))) ↔
      Integrable F planePairMeasure := by
  simp_rw [planeCoordinate_real_smul]
  rw [integrable_comp_smul_iff volume (fun z => F ((starRingEnd ℂ) z)) (inv_ne_zero (by positivity : Real.sqrt 2*ell ≠ 0)),
    plane_integrable_conj_iff, planePairMeasure,
    integrable_smul_measure (by positivity : ENNReal.ofReal (2/Real.pi) ≠ 0)
      ENNReal.ofReal_ne_top]

end VortexGap.Fermion
