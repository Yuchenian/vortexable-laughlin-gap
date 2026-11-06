import VortexGap.Geometry.PlaneEvaluation
import VortexGap.Geometry.PlanePositionSynthesis
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory

theorem planeCoordinate_double_scale (ell : ℝ) (hell : 0 < ell) (z : ℂ) :
    planeCoordinate ell ((2*ell : ℝ) • z) = (Real.sqrt 2 : ℂ)*z := by
  have he : (ell : ℂ) ≠ 0 := by exact_mod_cast hell.ne'
  have hs : (Real.sqrt 2 : ℂ)^2 = 2 := by exact_mod_cast Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hn : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast (show Real.sqrt 2 ≠ 0 by positivity)
  dsimp [planeCoordinate]
  simp only [Complex.ofReal_mul, Complex.ofReal_ofNat]
  field_simp
  linear_combination -z * hs

theorem planePairAmplitude_sqrt_scale (z : ℂ) (n : ℕ) :
    planePairAmplitude z (n+1) = (Real.exp (-‖z‖^2) : ℂ)*
      planeBargmannCoeff ((Real.sqrt 2 : ℂ)*z) n := by
  have hs : Real.sqrt ((2 : ℝ)^n) = (Real.sqrt 2)^n := by
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [Real.sq_sqrt (by positivity), ← pow_mul, Nat.mul_comm n 2, pow_mul,
      Real.sq_sqrt (by norm_num)]
  simp only [planePairAmplitude, Nat.add_sub_cancel_right, planeBargmannCoeff, mul_pow]
  rw [Real.sqrt_div (by positivity), hs]
  push_cast
  ring
theorem planeWavefunction_double_scale (ell : ℝ) (hell : 0 < ell) (z : ℂ) (n : ℕ) :
    planeWavefunction ell ((2*ell : ℝ) • z) n =
      ((Real.sqrt (2*Real.pi*ell^2))⁻¹ : ℂ)*planePairAmplitude z (n+1) := by
  rw [planeWavefunction, planeCoordinate_double_scale ell hell z, planePairAmplitude_sqrt_scale]
  have hn : ‖(Real.sqrt 2 : ℂ)*z‖^2/2 = ‖z‖^2 := by
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (by norm_num)]
    ring
  rw [neg_div, hn]
  ring

theorem planeWavefunction_amplitude (ell : ℝ) (hell : 0 < ell) (z : ℂ) (n : ℕ) :
    planeWavefunction ell z n = ((Real.sqrt (2*Real.pi*ell^2))⁻¹ : ℂ)*
      planePairAmplitude ((2*ell : ℝ)⁻¹ • z) (n+1) := by
  have h := planeWavefunction_double_scale ell hell ((2*ell : ℝ)⁻¹ • z) n
  rw [smul_smul, mul_inv_cancel₀ (by positivity : (2*ell : ℝ) ≠ 0), one_smul] at h
  exact h

theorem planeEvaluation_amplitude_series (ell : ℝ) (hell : 0 < ell)
    (z : ℂ) (v : CountableOrbital) :
    inner ℂ (planeEvaluation ell z) v = ((Real.sqrt (2*Real.pi*ell^2))⁻¹ : ℂ)*
      ∑' n, v n * planePairAmplitude ((2*ell : ℝ)⁻¹ • z) (n+1) := by
  have h := (planeAmplitude_series_summable v ((2*ell : ℝ)⁻¹ • z)).hasSum.mul_left
    (((Real.sqrt (2*Real.pi*ell^2))⁻¹ : ℂ))
  apply (planeEvaluation_hasSum ell z v).unique
  convert h using 1
  funext n
  rw [planeWavefunction_amplitude ell hell z n]
  ring

theorem planeAmplitude_series_integral_volume (v : CountableOrbital) :
    (∫ z : ℂ, ‖∑' n, v n * planePairAmplitude z (n+1)‖^2) = (Real.pi/2)*‖v‖^2 := by
  have h := planeAmplitude_series_integral v
  rw [planePairMeasure, integral_smul_measure, ENNReal.toReal_ofReal (by positivity), smul_eq_mul] at h
  have hp : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp at h
  nlinarith

theorem planeEvaluation_integral_norm_sq (ell : ℝ) (hell : 0 < ell) (v : CountableOrbital) :
    (∫ z : ℂ, ‖inner ℂ (planeEvaluation ell z) v‖^2) = ‖v‖^2 := by
  simp_rw [planeEvaluation_amplitude_series ell hell, norm_mul, mul_pow]
  rw [integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg volume (fun z : ℂ => ‖∑' n, v n * planePairAmplitude z (n+1)‖^2)
    (show (0 : ℝ) ≤ 2*ell by positivity), Complex.finrank_real_complex, smul_eq_mul,
    planeAmplitude_series_integral_volume]
  simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), inv_pow]
  rw [Real.sq_sqrt (by positivity)]
  field_simp

end VortexGap.Fermion




