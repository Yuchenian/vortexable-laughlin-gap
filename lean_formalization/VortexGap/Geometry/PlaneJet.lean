import VortexGap.Geometry.PlaneCoherent
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped InnerProduct ENNReal

theorem plane_exp_first_moment (t : ℝ) :
    HasSum (fun n : ℕ => (n : ℝ)*t^n/(n.factorial : ℝ)) (t*Real.exp t) := by
  rw [← hasSum_nat_add_iff' 1]
  convert (NormedSpace.expSeries_div_hasSum_exp t).mul_left t using 1
  · funext n
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
    have hn : (n : ℝ)+1 ≠ 0 := by positivity
    field_simp
  · simp [Real.exp_eq_exp_ℝ]

theorem plane_exp_successor_moment (t : ℝ) :
    HasSum (fun n : ℕ => ((n : ℝ)+1)*t^n/(n.factorial : ℝ))
      ((t+1)*Real.exp t) := by
  have h := (plane_exp_first_moment t).add
    (show HasSum (fun n : ℕ => t^n/(n.factorial : ℝ)) (Real.exp t) by
      simpa only [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp t)
  convert h using 1 <;> (try funext n) <;> ring

/-- Coefficients of the holomorphic Bargmann derivative. Hilbert differentiability
is proved separately; this definition does not assume it. -/
def planeJetCoeff (z : ℂ) : ℕ → ℂ
  | 0 => 0
  | n+1 => (n+1 : ℂ)*z^n / (Real.sqrt ((n+1).factorial : ℝ) : ℂ)

theorem planeJetCoeff_norm_sq_succ (z : ℂ) (n : ℕ) :
    ‖planeJetCoeff z (n+1)‖^2 = ((n : ℝ)+1)*(‖z‖^2)^n/(n.factorial : ℝ) := by
  have hnrm : ‖(n+1 : ℂ)‖ = (n : ℝ)+1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using Complex.norm_natCast (n+1)
  simp only [planeJetCoeff, norm_div, norm_mul, norm_pow, div_pow, mul_pow,
    hnrm, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [Real.sq_sqrt (by positivity)]
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  rw [← pow_mul, Nat.mul_comm n 2, pow_mul]
  have hn : (n : ℝ)+1 ≠ 0 := by positivity
  field_simp

theorem planeJetCoeff_hasSum_norm_sq (z : ℂ) :
    HasSum (fun n => ‖planeJetCoeff z n‖^2)
      ((‖z‖^2+1)*Real.exp (‖z‖^2)) := by
  rw [← hasSum_nat_add_iff' 1]
  simpa only [planeJetCoeff_norm_sq_succ, Finset.sum_range_one,
    show planeJetCoeff z 0 = 0 from rfl, norm_zero, zero_pow (by decide : 2 ≠ 0), sub_zero] using
      plane_exp_successor_moment (‖z‖^2)

def planeJet (z : ℂ) : CountableOrbital :=
  ⟨planeJetCoeff z, by
    apply memℓp_gen
    simpa only [show (2 : ℝ≥0∞).toReal = (2 : ℝ) by norm_num, Real.rpow_two] using
      (planeJetCoeff_hasSum_norm_sq z).summable⟩

theorem planeJet_norm_sq (z : ℂ) :
    ‖planeJet z‖^2 = (‖z‖^2+1)*Real.exp (‖z‖^2) := by
  calc
    _ = ∑' n, ‖planeJetCoeff z n‖^2 := by
      simpa [planeJet] using lp.norm_rpow_eq_tsum
        (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal) (planeJet z)
    _ = _ := (planeJetCoeff_hasSum_norm_sq z).tsum_eq

theorem planeBargmannCoeff_hasDerivAt (z : ℂ) (n : ℕ) :
    HasDerivAt (fun w => planeBargmannCoeff w n) (planeJetCoeff z n) z := by
  cases n with
  | zero => simpa [planeBargmannCoeff, planeJetCoeff] using hasDerivAt_const z (1 : ℂ)
  | succ n =>
    simpa [planeBargmannCoeff, planeJetCoeff, Nat.cast_add, Nat.cast_one] using
      ((hasDerivAt_id z).pow (n+1)).div_const (Real.sqrt ((n+1).factorial : ℝ) : ℂ)

end VortexGap.Fermion
