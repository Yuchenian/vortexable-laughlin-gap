import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

noncomputable section

namespace VortexGap.Fermion
open scoped BoundedContinuousFunction

def periodicWeight (ε q : ℝ) (z : ℂ) : ℝ :=
  1 + ε / 2 * (Real.cos (q * z.re) + Real.cos (q * z.im))

theorem periodicWeight_bounds {ε : ℝ} (hε : 0 ≤ ε) (q : ℝ) (z : ℂ) :
    1 - ε ≤ periodicWeight ε q z ∧ periodicWeight ε q z ≤ 1 + ε := by
  unfold periodicWeight
  constructor
  · nlinarith [mul_nonneg hε (add_nonneg
      (show 0 ≤ 1 + Real.cos (q*z.re) by linarith [Real.neg_one_le_cos (q*z.re)])
      (show 0 ≤ 1 + Real.cos (q*z.im) by linarith [Real.neg_one_le_cos (q*z.im)]))]
  · nlinarith [mul_nonneg hε (add_nonneg (sub_nonneg.mpr (Real.cos_le_one (q*z.re)))
      (sub_nonneg.mpr (Real.cos_le_one (q*z.im))))]

def periodicEnvelope (ε q : ℝ) (hε : 0 ≤ ε) : ℂ →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun z => ((Real.sqrt (periodicWeight ε q z) : ℝ) : ℂ))
    (by unfold periodicWeight; fun_prop) (Real.sqrt (1 + ε)) (fun z => by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact Real.sqrt_le_sqrt (periodicWeight_bounds hε q z).2)

theorem periodicEnvelope_norm_sq {ε : ℝ} (hε : 0 ≤ ε) (hε' : ε < 1) (q : ℝ) (z : ℂ) :
    ‖periodicEnvelope ε q hε z‖^2 = periodicWeight ε q z := by
  change ‖((Real.sqrt _ : ℝ) : ℂ)‖^2 = _
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt]
  linarith [(periodicWeight_bounds hε q z).1]

theorem periodicEnvelope_differentiable {ε : ℝ} (hε : 0 ≤ ε) (hε' : ε < 1) (q : ℝ) :
    Differentiable ℝ (periodicEnvelope ε q hε) := by
  intro z
  have hp : 0 < periodicWeight ε q z := by linarith [(periodicWeight_bounds hε q z).1]
  change DifferentiableAt ℝ (fun w : ℂ => ((Real.sqrt (periodicWeight ε q w) : ℝ) : ℂ)) z
  have hw : DifferentiableAt ℝ (periodicWeight ε q) z := by unfold periodicWeight; fun_prop
  exact Complex.ofRealCLM.differentiableAt.comp z (hw.sqrt hp.ne')

private theorem cos_phases (s : ℝ) :
    (Real.cos s : ℂ) = (Complex.exp (Complex.I * (s : ℂ)) +
      Complex.exp (-(Complex.I * (s : ℂ)))) / 2 := by
  rw [Complex.ofReal_cos, Complex.cos]
  simp [mul_comm]

/-- Exactly the four nonconstant Fourier modes in the positive-envelope example. -/
theorem periodicEnvelope_modes {ε : ℝ} (hε : 0 ≤ ε) (hε' : ε < 1) (q : ℝ) (z : ℂ) :
    ((‖periodicEnvelope ε q hε z‖ ^ 2 : ℝ) : ℂ) - 1 =
      (ε : ℂ) / 4 * (Complex.exp (Complex.I * ((q*z.re : ℝ) : ℂ)) +
        Complex.exp (-(Complex.I * ((q*z.re : ℝ) : ℂ))) +
        Complex.exp (Complex.I * ((q*z.im : ℝ) : ℂ)) +
        Complex.exp (-(Complex.I * ((q*z.im : ℝ) : ℂ)))) := by
  rw [periodicEnvelope_norm_sq hε hε']
  unfold periodicWeight
  simp only [Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat]
  rw [cos_phases, cos_phases]; simp only [Complex.ofReal_mul]
  ring

theorem periodicEnvelope_pair_lower {ε : ℝ} (hε : 0 ≤ ε) (hε' : ε < 1) (q : ℝ) (z : ℂ) :
    (1 - ε)^2 ≤ ‖periodicEnvelope ε q hε z‖^4 := by
  rw [show (4:ℕ) = 2 * 2 by decide, pow_mul, periodicEnvelope_norm_sq hε hε']
  exact pow_le_pow_left₀ (by linarith) (periodicWeight_bounds hε q z).1 2

/-- Two axis directions and their negatives, indexed with multiplicity
so that the expansion also applies when q vanishes. -/
def periodicFrequencies (q : ℝ) : Fin 4 → ℂ := ![⟨q,0⟩, ⟨-q,0⟩, ⟨0,q⟩, ⟨0,-q⟩]

theorem periodicEnvelope_symbol {ε : ℝ} (hε : 0 ≤ ε) (hε' : ε < 1) (q : ℝ) (z : ℂ) :
    ((‖periodicEnvelope ε q hε z‖^2 : ℝ) : ℂ) =
      1 + ∑ i : Fin 4, ((ε/4 : ℝ) : ℂ) *
        Complex.exp (Complex.I * (((periodicFrequencies q i).re*z.re +
          (periodicFrequencies q i).im*z.im : ℝ) : ℂ)) := by
  have h := periodicEnvelope_modes hε hε' q z

  simp [Fin.sum_univ_four, periodicFrequencies, Complex.ofReal_neg, neg_mul, mul_neg]
  simp [mul_assoc] at h ⊢
  linear_combination h

theorem periodicFrequencies_norm_sq (q : ℝ) (i : Fin 4) : ‖periodicFrequencies q i‖^2 = q^2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; fin_cases i <;> simp [periodicFrequencies, pow_two]

theorem periodicEnvelope_nonconstant {ε q : ℝ} (hε : 0 < ε) (hε' : ε < 1) (hq : q ≠ 0) :
    periodicEnvelope ε q hε.le 0 ≠ periodicEnvelope ε q hε.le ((Real.pi / q : ℝ) : ℂ) := by
  intro he
  have h := congrArg (fun w : ℂ => ‖w‖^2) he
  change ‖periodicEnvelope ε q hε.le 0‖^2 = ‖periodicEnvelope ε q hε.le _‖^2 at h
  rw [periodicEnvelope_norm_sq hε.le hε', periodicEnvelope_norm_sq hε.le hε'] at h
  simp [periodicWeight, show q * (Real.pi / q) = Real.pi by field_simp] at h
  linarith

end VortexGap.Fermion

namespace VortexGap.Fermion

/-- A rational majorant for the first harmonic, raised to the fourth power
for the second harmonic. Both estimates use the physical magnetic-cell scale. -/
theorem periodicMagnetic_attenuation :
    Real.exp (-(Real.pi/2)) < 21/100 ∧ Real.exp (-(2*Real.pi)) < 1/500 := by
  have he : (100/21:ℝ) < Real.exp (Real.pi/2) := by
    calc
      _ < ∑ i ∈ Finset.range 7, (1.57 : ℝ)^i / i.factorial := by
        norm_num [Finset.sum_range_succ, Nat.factorial]
      _ ≤ Real.exp 1.57 := Real.sum_le_exp_of_nonneg (by norm_num) _
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith [Real.pi_gt_d2])
  have h : Real.exp (-(Real.pi/2)) < 21/100 := by
    rw [Real.exp_neg, inv_eq_one_div, div_lt_div_iff₀ (Real.exp_pos _) (by norm_num)]
    linarith
  refine ⟨h, ?_⟩
  rw [show -(2*Real.pi) = (4:ℕ) * (-(Real.pi/2)) by push_cast; ring, Real.exp_nat_mul]
  exact (pow_lt_pow_left₀ h (Real.exp_pos _).le (by decide : (4:ℕ) ≠ 0)).trans (by norm_num)

def periodicGapBound (κ α γ : ℝ) : ℝ :=
  κ / (1-α)^2 * (γ-14*(1-(1-α)/(1+α))-(1-(1-α)/(1+α))^2)

theorem periodic_first_row_arithmetic :
    (1390/10000:ℝ) < periodicGapBound ((1-1/100)^2) (21/10000) (1/5) := by
  norm_num [periodicGapBound]

theorem periodic_path_arithmetic {ε : ℝ} (hmax : ε ≤ 1/2) :
    (430/10000:ℝ) < periodicGapBound ((1-ε)^2) (1/1000) (1/5) := by
  have hh : (1/2:ℝ)^2 ≤ (1-ε)^2 := pow_le_pow_left₀ (by norm_num) (by linarith) 2
  unfold periodicGapBound
  norm_num at hh ⊢
  nlinarith

def periodicMagneticWaveNumber (ell : ℝ) (n : ℕ) := n * Real.sqrt (2*Real.pi) / ell

theorem periodicMagnetic_scale (ell : ℝ) (hell : 0 < ell) (n : ℕ) :
    -(periodicMagneticWaveNumber ell n)^2 * ell^2 / 4 = -((n:ℝ)^2 * Real.pi / 2) := by
  unfold periodicMagneticWaveNumber
  rw [div_pow, mul_pow, Real.sq_sqrt (by positivity)]
  field_simp
  ring

theorem periodicMagnetic_first (ell : ℝ) (hell : 0 < ell) :
    (1/100:ℝ) * Real.exp (-(periodicMagneticWaveNumber ell 1)^2 * ell^2 / 4) ≤ 21/10000 := by
  rw [periodicMagnetic_scale ell hell]
  norm_num only [Nat.cast_one, one_pow, one_mul]
  linarith [periodicMagnetic_attenuation.1]

theorem periodicMagnetic_path (ell : ℝ) (hell : 0 < ell) (ε : ℝ) (hmax : ε ≤ 1/2) :
    ε * Real.exp (-(periodicMagneticWaveNumber ell 2)^2 * ell^2 / 4) ≤ 1/1000 := by
  rw [periodicMagnetic_scale ell hell, show -((↑(2:ℕ):ℝ)^2 * Real.pi / 2) = -(2*Real.pi) by norm_num; ring]
  exact (mul_le_mul_of_nonneg_right hmax (Real.exp_pos _).le).trans (by linarith [periodicMagnetic_attenuation.2])

end VortexGap.Fermion
