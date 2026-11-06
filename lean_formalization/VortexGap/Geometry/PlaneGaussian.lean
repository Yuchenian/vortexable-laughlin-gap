import VortexGap.Geometry.PlanePairAmplitude
import Mathlib.MeasureTheory.Integral.Gamma
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory

theorem plane_gaussian_moment (b : ℝ) (hb : 0 < b) (n : ℕ) :
    (∫ z : ℂ, ‖z‖^(2*n)*Real.exp (-b*‖z‖^2)) =
      Real.pi*(n.factorial : ℝ)/b^(n+1) := by
  have h := Complex.integral_rpow_mul_exp_neg_mul_rpow
    (p := 2) (q := ((2*n : ℕ) : ℝ)) (b := b) (by norm_num) (by
      have hn : (0 : ℝ) ≤ ((2*n : ℕ) : ℝ) := by positivity
      linarith) hb
  have he : (((2*n : ℕ) : ℝ)+2)/2 = (n : ℝ)+1 := by push_cast; ring
  have he' : -(((2*n : ℕ) : ℝ)+2)/2 = -((n : ℝ)+1) := by push_cast; ring
  rw [he, he', Real.Gamma_nat_eq_factorial, Real.rpow_neg hb.le] at h
  have hc : (n : ℝ)+1 = ((n+1 : ℕ) : ℝ) := by push_cast; rfl
  rw [hc, Real.rpow_natCast] at h
  simp only [Real.rpow_natCast, Real.rpow_two] at h
  convert h using 1
  ring

/-- Integrability follows from the proved nonzero integral value; Lean's
Bochner integral would be zero for a nonintegrable function. -/
theorem plane_gaussian_moment_integrable (b : ℝ) (hb : 0 < b) (n : ℕ) :
    Integrable (fun z : ℂ => ‖z‖^(2*n)*Real.exp (-b*‖z‖^2)) := by
  by_contra h
  have he := plane_gaussian_moment b hb n
  rw [integral_undef h] at he
  have hp : 0 < Real.pi*(n.factorial : ℝ)/b^(n+1) := by positivity
  linarith

theorem planePairAmplitude_norm_sq_density (z : ℂ) (n : ℕ) :
    ‖planePairAmplitude z (n+1)‖^2 = ((2 : ℝ)^n/(n.factorial : ℝ))*
      (‖z‖^(2*n)*Real.exp (-2*‖z‖^2)) := by
  simp only [planePairAmplitude_norm_sq, Nat.add_sub_cancel_right, mul_pow, ← pow_mul, neg_mul]
  ring

theorem planePairAmplitude_integral_volume (n : ℕ) :
    (∫ z : ℂ, ‖planePairAmplitude z (n+1)‖^2) = Real.pi/2 := by
  simp_rw [planePairAmplitude_norm_sq_density]
  rw [integral_const_mul, plane_gaussian_moment 2 (by norm_num) n, pow_succ]
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  field_simp

/-- The actual coherent-pair position measure specified by the current supplement. -/
def planePairMeasure : Measure ℂ := ENNReal.ofReal (2/Real.pi) • volume

instance planePairMeasure_sigmaFinite : SigmaFinite planePairMeasure := by
  dsimp [planePairMeasure]
  haveI : IsFiniteMeasureOnCompacts (ENNReal.ofReal (2/Real.pi) • (volume : Measure ℂ)) :=
    IsFiniteMeasureOnCompacts.smul volume ENNReal.ofReal_ne_top
  infer_instance

theorem planePairAmplitude_continuous (n : ℕ) : Continuous (fun z : ℂ => planePairAmplitude z n) := by
  unfold planePairAmplitude
  fun_prop

/-- Every positive angular amplitude has L2 norm one in the actual plane measure. -/
theorem planePairAmplitude_integral (n : ℕ) :
    (∫ z : ℂ, ‖planePairAmplitude z (n+1)‖^2 ∂planePairMeasure) = 1 := by
  rw [planePairMeasure, integral_smul_measure, ENNReal.toReal_ofReal (by positivity),
    smul_eq_mul, planePairAmplitude_integral_volume]
  field_simp

theorem planePairAmplitude_memLp (n : ℕ) :
    MemLp (fun z : ℂ => planePairAmplitude z (n+1)) 2 planePairMeasure := by
  apply (memLp_two_iff_integrable_sq_norm (planePairAmplitude_continuous (n+1)).aestronglyMeasurable).2
  apply Integrable.of_integral_ne_zero
  rw [planePairAmplitude_integral]
  norm_num

end VortexGap.Fermion
