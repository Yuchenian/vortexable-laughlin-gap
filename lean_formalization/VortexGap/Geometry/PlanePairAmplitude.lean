import VortexGap.Geometry.PlaneBlockCoordinates
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped InnerProduct

def planePairAmplitude (z : ℂ) (n : ℕ) : ℂ :=
  (Real.exp (-‖z‖^2) : ℂ) *
    (Real.sqrt ((2 : ℝ)^(n-1)/((n-1).factorial : ℝ)) : ℂ) * z^(n-1)

theorem planeBlockCoefficient_radial_scale (n : ℕ) (hn : 0 < n) (i : ℕ) (hi : i ≤ n) :
    Real.sqrt ((2 : ℝ)^(n-1)/((n-1).factorial : ℝ))*planeBlockCoefficient n i =
      ((n : ℝ)-2*(i : ℝ))/Real.sqrt ((i.factorial : ℝ)*((n-i).factorial : ℝ)) := by
  rw [planeBlockCoefficient_factorial n hn i hi]
  have hf : ((n-1).factorial : ℝ) ≠ 0 := by positivity
  have hp : (2 : ℝ)^(n-1) ≠ 0 := by positivity
  calc
    _ = ((n : ℝ)-2*(i : ℝ))*Real.sqrt
        (((2 : ℝ)^(n-1)/((n-1).factorial : ℝ))*
          (((n-1).factorial : ℝ)/((2 : ℝ)^(n-1)*(i.factorial : ℝ)*((n-i).factorial : ℝ)))) := by
      rw [Real.sqrt_mul (by positivity)]
      ring
    _ = ((n : ℝ)-2*(i : ℝ))*Real.sqrt (1/((i.factorial : ℝ)*((n-i).factorial : ℝ))) := by
      congr 1
      congr 1
      field_simp
    _ = _ := by rw [Real.sqrt_div (by positivity), Real.sqrt_one]; ring

/-- Separation of the actual coherent-pair coefficient into its angular block
vector and a common radial/phase amplitude, including z=0. -/
theorem planeTwoFramePair_block_coordinate (z : ℂ) (a : CountablePairIndex) :
    countableTwoFramePair (planeTwoFrame z) a =
      planePairAmplitude z (a.val.1+a.val.2) * planeBlockVector (a.val.1+a.val.2) a := by
  let n := a.val.1+a.val.2
  have hn : 0 < n := by dsimp [n]; have := a.property; omega
  have hi : a.val.1 ≤ n := by dsimp [n]; omega
  have hj : n-a.val.1 = a.val.2 := by dsimp [n]; omega
  have hs : (Real.sqrt ((2 : ℝ)^(n-1)/((n-1).factorial : ℝ)) : ℂ)*
      (planeBlockCoefficient n a.val.1 : ℂ) =
      ((a.val.2 : ℂ)-(a.val.1 : ℂ))/
        (Real.sqrt ((a.val.1.factorial : ℝ)*(a.val.2.factorial : ℝ)) : ℂ) := by
    have hr := planeBlockCoefficient_radial_scale n hn a.val.1 hi
    rw [hj] at hr
    have he : (n : ℝ)-2*(a.val.1 : ℝ) = (a.val.2 : ℝ)-(a.val.1 : ℝ) := by
      dsimp [n]; push_cast; ring
    rw [he] at hr
    exact_mod_cast hr
  rw [planeTwoFramePair_coefficient, planeBlockVector_coordinate, ite_eq_left rfl]
  change (Real.exp (-‖z‖^2) : ℂ)*((a.val.2 : ℂ)-(a.val.1 : ℂ))*z^(n-1)/
    (Real.sqrt ((a.val.1.factorial : ℝ)*(a.val.2.factorial : ℝ)) : ℂ) =
      ((Real.exp (-‖z‖^2) : ℂ)*(Real.sqrt ((2 : ℝ)^(n-1)/((n-1).factorial : ℝ)) : ℂ)*
        z^(n-1))*(planeBlockCoefficient n a.val.1 : ℂ)
  calc
    _ = (Real.exp (-‖z‖^2) : ℂ)*z^(n-1)*
        ((Real.sqrt ((2 : ℝ)^(n-1)/((n-1).factorial : ℝ)) : ℂ)*
          (planeBlockCoefficient n a.val.1 : ℂ)) := by rw [hs]; ring
    _ = _ := by ring

theorem planePairAmplitude_norm_sq (z : ℂ) (n : ℕ) :
    ‖planePairAmplitude z n‖^2 = Real.exp (-(2*‖z‖^2))*
      ((2*‖z‖^2)^(n-1)/((n-1).factorial : ℝ)) := by
  simp only [planePairAmplitude, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), abs_of_nonneg (Real.sqrt_nonneg _), mul_pow]
  rw [Real.sq_sqrt (by positivity), ← Real.exp_nat_mul]
  have he : (2 : ℕ)*(-‖z‖^2) = -(2*‖z‖^2) := by ring
  rw [he, ← pow_mul, Nat.mul_comm (n-1) 2, pow_mul]
  ring

/-- Exact probability normalization of all positive angular block amplitudes.
This is a pointwise infinite sum, not the position-integrated frame identity. -/
theorem planePairAmplitude_hasSum_norm_sq (z : ℂ) :
    HasSum (fun n : ℕ => ‖planePairAmplitude z (n+1)‖^2) 1 := by
  have h := (NormedSpace.expSeries_div_hasSum_exp (2*‖z‖^2)).mul_left
    (Real.exp (-(2*‖z‖^2)))
  have he : Real.exp (-(2*‖z‖^2))*Real.exp (2*‖z‖^2) = 1 := by
    rw [← Real.exp_add]
    simp
  simpa only [planePairAmplitude_norm_sq, Nat.add_sub_cancel_right,
    ← Real.exp_eq_exp_ℝ, he] using h

end VortexGap.Fermion
