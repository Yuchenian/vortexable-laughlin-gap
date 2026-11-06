import VortexGap.Geometry.PlaneTraceNorm
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion

/-- Radial Schur integral at flux n+1 in t=cos(theta/2) coordinates.
The normalized radial probability measure is 2t dt. -/
def sphereRadialSchur (n : ℕ) : ℝ :=
  2*(2*(n:ℝ)+1) * ∫ t in (0:ℝ)..1, t^n * Real.sqrt (4*t^2+(n:ℝ)^2*(1-t^2)^2)

private theorem unit_moment (n : ℕ) :
    (∫ t in (0:ℝ)..1, t^n) = 1/((n:ℝ)+1) := by
  rw [integral_pow]
  simp

private theorem weighted_moment (n : ℕ) :
    (∫ t in (0:ℝ)..1, t^n*(4*t^2+(n:ℝ)^2*(1-t^2)^2)) =
      (12*((n:ℝ)+1)^2+8)/(((n:ℝ)+1)*((n:ℝ)+3)*((n:ℝ)+5)) := by
  have he (t : ℝ) : t^n*(4*t^2+(n:ℝ)^2*(1-t^2)^2) =
      (n:ℝ)^2*t^n + (4-2*(n:ℝ)^2)*t^(n+2) + (n:ℝ)^2*t^(n+4) := by
    simp only [pow_add]
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_add, intervalIntegral.integral_add]
  · simp only [intervalIntegral.integral_const_mul,unit_moment,Nat.cast_add,Nat.cast_ofNat]
    field_simp
    ring
  all_goals exact Continuous.intervalIntegrable (by fun_prop) ..

theorem sphereRadialSchur_le (n : ℕ) :
    sphereRadialSchur n ≤ 2*(2*(n:ℝ)+1)/((n:ℝ)+1) *
      Real.sqrt ((12*((n:ℝ)+1)^2+8)/(((n:ℝ)+3)*((n:ℝ)+5))) := by
  let m := (12*((n:ℝ)+1)^2+8)/(((n:ℝ)+3)*((n:ℝ)+5))
  have hm : 0 < m := by dsimp [m]; positivity
  let r := Real.sqrt m
  have hr : 0 < r := Real.sqrt_pos.mpr hm
  have hr2 : r^2 = m := Real.sq_sqrt hm.le
  let a := fun t : ℝ => 4*t^2+(n:ℝ)^2*(1-t^2)^2
  have hi : (∫ t in (0:ℝ)..1, t^n*Real.sqrt (a t)) ≤
      ∫ t in (0:ℝ)..1, (t^n*a t + m*t^n)/(2*r) := by
    apply intervalIntegral.integral_mono_on (by norm_num)
      (Continuous.intervalIntegrable (by dsimp [a]; fun_prop) ..)
      (Continuous.intervalIntegrable (by dsimp [a]; fun_prop) ..)
    intro t ht
    rw [le_div_iff₀ (by positivity)]
    have ha : 0 ≤ a t := by dsimp [a]; positivity
    have h := mul_nonneg (pow_nonneg ht.1 n) (sq_nonneg (Real.sqrt (a t)-r))
    nlinarith only [h,congrArg (fun x : ℝ => t^n*x) hr2,
      congrArg (fun x : ℝ => t^n*x) (Real.sq_sqrt ha)]
  have havg : (∫ t in (0:ℝ)..1, t^n*a t) = m/((n:ℝ)+1) := by
    rw [show (∫ t in (0:ℝ)..1, t^n*a t) = _ from weighted_moment n]
    dsimp [m]
    field_simp
  rw [intervalIntegral.integral_div,intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by dsimp [a]; fun_prop) ..)
    (Continuous.intervalIntegrable (by fun_prop) ..),intervalIntegral.integral_const_mul,
    unit_moment,havg] at hi
  change 2*(2*(n:ℝ)+1)*_ ≤ _*r
  apply (mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ 2*(2*(n:ℝ)+1))).trans_eq
  rw [← hr2]
  field_simp; ring

theorem sphereRadialSchur_lt (n : ℕ) : sphereRadialSchur n < 8*Real.sqrt 3 := by
  apply (sphereRadialSchur_le n).trans_lt
  have h1 : 2*(2*(n:ℝ)+1)/((n:ℝ)+1) < 4 := by rw [div_lt_iff₀ (by positivity)]; linarith
  have h2 : Real.sqrt ((12*((n:ℝ)+1)^2+8)/(((n:ℝ)+3)*((n:ℝ)+5))) < 2*Real.sqrt 3 := by
    apply (sq_lt_sq₀ (by positivity) (by positivity)).mp
    rw [Real.sq_sqrt (by positivity),mul_pow,Real.sq_sqrt (by norm_num),div_lt_iff₀ (by positivity)]
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  calc
    _ < 4*(2*Real.sqrt 3) := lt_of_le_of_lt (mul_le_mul_of_nonneg_right h1.le (Real.sqrt_nonneg _)) (mul_lt_mul_of_pos_left h2 (by norm_num))
    _ = _ := by ring

theorem sphereRadialSchur_lt_fourteen (n : ℕ) : sphereRadialSchur n < 14 :=
  (sphereRadialSchur_lt n).trans (by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)])

theorem sphereRadialSchur_flux_one : sphereRadialSchur 0 = 2 := by
  unfold sphereRadialSchur
  simp only [Nat.cast_zero,pow_zero,zero_pow (by decide : 2 ≠ 0),zero_mul,add_zero,
    one_mul]
  have h : (∫ t in (0:ℝ)..1, √(4*t^2)) = ∫ t in (0:ℝ)..1, 2*t := by
    apply intervalIntegral.integral_congr
    intro t ht
    change √(4*t^2) = 2*t
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
    rw [show 4*t^2 = (2*t)^2 by ring,Real.sqrt_sq (mul_nonneg (by norm_num) ht.1)]
  rw [h,intervalIntegral.integral_const_mul,integral_id]
  norm_num
theorem sphereRadialSchur_flux_two : sphereRadialSchur 1 = 9/2 := by
  unfold sphereRadialSchur
  have h : (∫ t in (0:ℝ)..1, t^1*√(4*t^2+(1:ℝ)^2*(1-t^2)^2)) =
      ∫ t in (0:ℝ)..1, t^1+t^3 := by
    apply intervalIntegral.integral_congr
    intro t _
    change t^1*√(4*t^2+(1:ℝ)^2*(1-t^2)^2) = t^1+t^3
    rw [show 4*t^2+(1:ℝ)^2*(1-t^2)^2 = (1+t^2)^2 by ring,Real.sqrt_sq (by positivity)]
    ring
  push_cast
  rw [h,intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) ..)
    (Continuous.intervalIntegrable (by fun_prop) ..),unit_moment,unit_moment]
  norm_num

end VortexGap.Fermion
