import VortexGap.Geometry.PlaneJet
import Mathlib.Analysis.Calculus.SmoothSeries
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped InnerProduct ENNReal

theorem planeJetCoeff_dilate (z : ℂ) (n : ℕ) :
    planeJetCoeff z n = (2*(1/2 : ℂ)^n)*planeJetCoeff (2*z) n := by
  cases n with
  | zero => simp [planeJetCoeff]
  | succ n =>
    simp only [planeJetCoeff, mul_pow, pow_succ, div_pow, one_pow]
    field_simp

/-- Absolute summability follows from l2 at doubled radius and a geometric l2
weight. This is used for uniform bounds on derivatives in a finite ball. -/
theorem planeJetCoeff_norm_summable (z : ℂ) : Summable (fun n => ‖planeJetCoeff z n‖) := by
  have hw (n : ℕ) : ‖(1/2 : ℂ)^n‖^2 = (1/4 : ℝ)^n := by
    rw [norm_pow]
    norm_num [norm_div]
    rw [← pow_mul, Nat.mul_comm n 2, pow_mul]
    norm_num
  let w : CountableOrbital := ⟨fun n => (1/2 : ℂ)^n, by
    apply memℓp_gen
    simpa only [show (2 : ℝ≥0∞).toReal = (2 : ℝ) by norm_num, Real.rpow_two, hw] using
      (summable_geometric_of_norm_lt_one (by norm_num : ‖(1/4 : ℝ)‖ < 1))⟩
  have hh := (lp.summable_mul (p := 2) (q := 2)
    (by rw [Real.holderConjugate_iff]; norm_num) (planeJet (2*z)) w).mul_left 2
  convert hh using 1
  funext n
  change ‖planeJetCoeff z n‖ = 2*(‖planeJetCoeff (2*z) n‖*‖(1/2 : ℂ)^n‖)
  rw [planeJetCoeff_dilate z n, norm_mul, norm_mul]
  norm_num
  ring

theorem planeJetCoeff_norm_mono (z : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hz : ‖z‖ ≤ r) (n : ℕ) :
    ‖planeJetCoeff z n‖ ≤ ‖planeJetCoeff (r : ℂ) n‖ := by
  cases n with
  | zero => simp [planeJetCoeff]
  | succ n =>
    simp only [planeJetCoeff, norm_div, norm_mul, norm_pow,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
    gcongr

/-- Genuine differentiation in the completed orbital Hilbert norm. The proof
uses a summable uniform derivative majorant on a ball, not coordinatewise
convergence alone. -/
theorem planeBargmann_hasDerivAt (z : ℂ) :
    HasDerivAt planeBargmann (planeJet z) z := by
  let r : ℝ := ‖z‖+1
  have hr : 0 < r := by dsimp [r]; positivity
  have hs (w : ℂ) :
      (∑' n, planeBargmannCoeff w n • orbitalKet n) = planeBargmann w :=
    (orbital_hasSum (planeBargmann w)).tsum_eq
  have hj : (∑' n, planeJetCoeff z n • orbitalKet n) = planeJet z :=
    (orbital_hasSum (planeJet z)).tsum_eq
  have h := hasDerivAt_tsum_of_isPreconnected
    (g := fun n w => planeBargmannCoeff w n • orbitalKet n)
    (g' := fun n w => planeJetCoeff w n • orbitalKet n)
    (t := Metric.ball (0 : ℂ) r) (y₀ := (0 : ℂ)) (y := z)
    (planeJetCoeff_norm_summable (r : ℂ)) Metric.isOpen_ball
    (convex_ball (0 : ℂ) r).isPreconnected
    (fun n w _ => (planeBargmannCoeff_hasDerivAt w n).smul_const (orbitalKet n))
    (by
      intro n w hw
      rw [norm_smul, orbitalKet_norm, mul_one]
      exact planeJetCoeff_norm_mono w r hr.le (le_of_lt (by simpa using hw)) n)
    (by simpa using hr)
    (orbital_hasSum (planeBargmann 0)).summable
    (by simp [r])
  simpa only [hs, hj] using h

/-- The derivative at the origin is a nonzero first oscillator mode, fixing
its phase and normalization for the later physical contact calculation. -/
theorem planeBargmann_deriv_zero : deriv planeBargmann 0 = orbitalKet 1 := by
  rw [(planeBargmann_hasDerivAt 0).deriv]
  ext n
  change planeJetCoeff 0 n = orbitalKet 1 n
  cases n with
  | zero => simp [planeJetCoeff, orbitalKet, lp.single_apply]
  | succ n =>
    by_cases hn : n = 0
    · subst n
      simp [planeJetCoeff, orbitalKet, lp.single_apply]
    · simp [planeJetCoeff, zero_pow hn, orbitalKet, lp.single_apply, hn]

end VortexGap.Fermion
