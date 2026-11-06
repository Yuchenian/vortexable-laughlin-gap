import VortexGap.Geometry.PlaneGaussian
import Mathlib.Analysis.Complex.Isometry
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory

theorem planePairAmplitude_rotation (r : Circle) (z : ℂ) (n : ℕ) :
    planePairAmplitude ((r : ℂ)*z) (n+1) =
      (r : ℂ)^n * planePairAmplitude z (n+1) := by
  simp only [planePairAmplitude, Nat.add_sub_cancel_right, norm_mul, Circle.norm_coe,
    one_mul, mul_pow]
  ring

theorem planePairMeasure_integral_rotation (r : Circle) (f : ℂ → ℂ) :
    (∫ z, f ((r : ℂ)*z) ∂planePairMeasure) = ∫ z, f z ∂planePairMeasure := by
  unfold planePairMeasure
  simp only [integral_smul_measure]
  congr 1
  simpa only [rotation_apply] using
    (rotation r).measurePreserving.integral_comp
      (rotation r).toHomeomorph.measurableEmbedding f

theorem circle_separates_powers_lt (m n : ℕ) (hmn : m < n) :
    ∃ r : Circle, (r : ℂ)^m ≠ (r : ℂ)^n := by
  let r := Circle.exp (Real.pi / ((n-m : ℕ) : ℝ))
  have hd : ((n-m : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.sub_ne_zero_of_lt hmn)
  have hr : r^(n-m) ≠ 1 := by
    dsimp [r]
    rw [← Circle.exp_natCast_mul]
    have he : ((n-m : ℕ) : ℝ)*(Real.pi / ((n-m : ℕ) : ℝ)) = Real.pi := by
      field_simp
    rw [he]
    exact Circle.exp_pi_ne_one
  refine ⟨r, ?_⟩
  intro he
  have he' : r^m = r^n := Subtype.ext (by simpa using he)
  have hn : n = m+(n-m) := by omega
  rw [hn, pow_add] at he'
  have hcancel : r^(n-m) = 1 := by
    apply mul_left_cancel (a := r^m)
    simpa using he'.symm
  exact hr hcancel

theorem circle_separates_powers (m n : ℕ) (hmn : m ≠ n) :
    ∃ r : Circle, (r : ℂ)^m ≠ (r : ℂ)^n := by
  rcases lt_or_gt_of_ne hmn with h | h
  · exact circle_separates_powers_lt m n h
  · obtain ⟨r, hr⟩ := circle_separates_powers_lt n m h
    exact ⟨r, Ne.symm hr⟩

theorem planePairAmplitude_integral_cross (m n : ℕ) (hmn : m ≠ n) :
    (∫ z : ℂ, (starRingEnd ℂ) (planePairAmplitude z (m+1)) *
      planePairAmplitude z (n+1) ∂planePairMeasure) = 0 := by
  obtain ⟨r, hr⟩ := circle_separates_powers m n hmn
  let c : ℂ := (starRingEnd ℂ) ((r : ℂ)^m) * (r : ℂ)^n
  have hunit : (r : ℂ)^m * (starRingEnd ℂ) ((r : ℂ)^m) = 1 := by
    rw [map_pow, ← Circle.coe_inv_eq_conj, Circle.coe_inv, ← mul_pow]
    simp
  have hc : c ≠ 1 := by
    intro he
    have hh := congrArg (fun x : ℂ => (r : ℂ)^m*x) he
    dsimp [c] at hh
    rw [← mul_assoc, hunit, one_mul, mul_one] at hh
    exact hr hh.symm
  let f := fun z : ℂ => (starRingEnd ℂ) (planePairAmplitude z (m+1)) * planePairAmplitude z (n+1)
  have hrot (z : ℂ) : f ((r : ℂ)*z) = c*f z := by
    dsimp [f, c]
    rw [planePairAmplitude_rotation, planePairAmplitude_rotation, map_mul]
    ring
  have hi : c * (∫ z, f z ∂planePairMeasure) = ∫ z, f z ∂planePairMeasure := by
    rw [← integral_const_mul]
    simp_rw [← hrot]
    exact planePairMeasure_integral_rotation r f
  have hz : (c-1)*(∫ z, f z ∂planePairMeasure) = 0 := by
    rw [sub_mul, hi, one_mul, sub_self]
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hc)

theorem planePairAmplitude_integrable_cross (m n : ℕ) :
    Integrable (fun z : ℂ => (starRingEnd ℂ) (planePairAmplitude z (m+1)) *
      planePairAmplitude z (n+1)) planePairMeasure := by
  exact (planePairAmplitude_memLp m).star.integrable_mul (planePairAmplitude_memLp n)

theorem planePairAmplitude_integral_inner (m n : ℕ) :
    (∫ z : ℂ, inner ℂ (planePairAmplitude z (m+1))
      (planePairAmplitude z (n+1)) ∂planePairMeasure) = if m = n then 1 else 0 := by
  by_cases h : m = n
  · subst n
    simp only [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, integral_ofReal, planePairAmplitude_integral,
      RCLike.ofReal_one, ite_true]
  · simp only [RCLike.inner_apply', planePairAmplitude_integral_cross m n h, ite_eq_right h]

end VortexGap.Fermion





