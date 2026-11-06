import VortexGap.Fermion.CountableOrbitalSpace
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Normed
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped InnerProduct ENNReal ComplexConjugate

/-- Unnormalized Bargmann coefficient; all oscillator modes are retained. -/
def planeBargmannCoeff (z : ℂ) (n : ℕ) : ℂ :=
  z^n / (Real.sqrt (n.factorial : ℝ) : ℂ)

theorem planeBargmannCoeff_norm_sq (z : ℂ) (n : ℕ) :
    ‖planeBargmannCoeff z n‖^2 = (‖z‖^2)^n / (n.factorial : ℝ) := by
  simp only [planeBargmannCoeff, norm_div, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), div_pow]
  rw [Real.sq_sqrt (by positivity), ← pow_mul, Nat.mul_comm n 2, pow_mul]

/-- The power series defines an actual vector of the completed one-particle space. -/
def planeBargmann (z : ℂ) : CountableOrbital :=
  ⟨planeBargmannCoeff z, by
    apply memℓp_gen
    simpa only [show (2 : ℝ≥0∞).toReal = (2 : ℝ) by norm_num,
      Real.rpow_two, planeBargmannCoeff_norm_sq] using
      Real.summable_pow_div_factorial (‖z‖^2)⟩

theorem planeBargmann_coefficient (z : ℂ) (n : ℕ) :
    planeBargmann z n = planeBargmannCoeff z n := rfl

theorem planeBargmann_norm_sq (z : ℂ) :
    ‖planeBargmann z‖^2 = Real.exp (‖z‖^2) := by
  calc
    _ = ∑' n, ‖planeBargmann z n‖^2 := by
      simpa using lp.norm_rpow_eq_tsum
        (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal) (planeBargmann z)
    _ = ∑' n : ℕ, (‖z‖^2)^n / (n.factorial : ℝ) := by
      simp only [planeBargmann_coefficient, planeBargmannCoeff_norm_sq]
    _ = _ := by rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]

/-- Coherent orbital D(z)|0>, with the Gaussian normalization in the current supplement. -/
def planeCoherent (z : ℂ) : CountableOrbital :=
  (Real.exp (-‖z‖^2/2) : ℂ) • planeBargmann z

theorem planeCoherent_norm_sq (z : ℂ) : ‖planeCoherent z‖^2 = 1 := by
  rw [planeCoherent, norm_smul, mul_pow, planeBargmann_norm_sq]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  have he : (2 : ℕ) * (-‖z‖^2/2) + ‖z‖^2 = (0 : ℝ) := by ring
  rw [he, Real.exp_zero]

theorem planeBargmannCoeff_inner (z w : ℂ) (n : ℕ) :
    inner ℂ (planeBargmannCoeff z n) (planeBargmannCoeff w n) =
      (conj z * w)^n / (n.factorial : ℂ) := by
  have hs : (Real.sqrt (n.factorial : ℝ) : ℂ)^2 = (n.factorial : ℂ) := by
    exact_mod_cast Real.sq_sqrt (show (0 : ℝ) ≤ n.factorial by positivity)
  simp only [RCLike.inner_apply', planeBargmannCoeff, map_div₀, map_pow, Complex.conj_ofReal]
  rw [div_mul_div_comm, ← pow_two, hs, ← mul_pow]

theorem planeBargmann_inner (z w : ℂ) :
    inner ℂ (planeBargmann z) (planeBargmann w) = Complex.exp (conj z * w) := by
  rw [lp.inner_eq_tsum]
  simp only [planeBargmann_coefficient, planeBargmannCoeff_inner]
  rw [Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div]

theorem planeCoherent_inner (z w : ℂ) :
    inner ℂ (planeCoherent z) (planeCoherent w) =
      (Real.exp (-‖z‖^2/2) : ℂ) * (Real.exp (-‖w‖^2/2) : ℂ) *
        Complex.exp (conj z * w) := by
  simp only [planeCoherent, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal, planeBargmann_inner]
  ring

end VortexGap.Fermion
