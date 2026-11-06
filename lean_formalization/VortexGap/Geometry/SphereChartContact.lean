import VortexGap.Geometry.SphereTraceNorm
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion

/-- Normalized north-chart monopole harmonic evaluated in the physical tangent coordinate z. -/
def sphereChartOrbital (Q j : ℕ) (R : ℝ) (z : ℂ) : ℂ :=
  (Real.sqrt (((Q+1:ℕ):ℝ)*(Q.choose j)/(4*Real.pi*R^2)) : ℂ) *
    (z/(2*R))^j / ((Real.sqrt (1+‖z/(2*R)‖^2) : ℂ)^Q)

theorem sphereChartOrbital_origin (Q j : ℕ) (R : ℝ) :
    sphereChartOrbital Q j R 0 = if j=0 then
      (Real.sqrt (((Q+1:ℕ):ℝ)/(4*Real.pi*R^2)) : ℂ) else 0 := by
  cases j <;> simp [sphereChartOrbital]

/-- Full directional jet in a physical tangent direction d at the north pole. -/
theorem sphereChartOrbital_jet (Q j : ℕ) (R : ℝ) (d : ℂ) :
    HasDerivAt (fun t : ℝ => sphereChartOrbital Q j R (t*d))
      (if j=1 then (Real.sqrt (((Q+1:ℕ):ℝ)*Q/(4*Real.pi*R^2)) : ℂ)*(d/(2*R)) else 0) 0 := by
  let b : ℂ := d/(2*R)
  let A : ℂ := Real.sqrt (((Q+1:ℕ):ℝ)*(Q.choose j)/(4*Real.pi*R^2))
  have hz : HasDerivAt (fun t : ℝ => (t:ℂ)*b) b 0 := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := (0:ℝ))).mul_const b
  have hh : HasDerivAt (fun t : ℝ => 1+t^2*‖b‖^2) 0 0 := by
    simpa using (((hasDerivAt_pow 2 (0:ℝ)).mul_const (‖b‖^2)).const_add 1)
  have hroot : HasDerivAt (fun t : ℝ => Real.sqrt (1+t^2*‖b‖^2)) 0 0 := by
    simpa using hh.sqrt (by norm_num)
  have hden := hroot.ofReal_comp.pow Q
  have hnum := (hz.pow j).const_mul A
  have hf := hnum.fun_div hden (by simp)
  have he (t : ℝ) : sphereChartOrbital Q j R (t*d) =
      A*((t:ℂ)*b)^j / (Real.sqrt (1+t^2*‖b‖^2) : ℂ)^Q := by
    simp [sphereChartOrbital,A,b, mul_div_assoc, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs]
  simp_rw [he]
  cases j with
  | zero => simpa [Pi.pow_apply] using! hf
  | succ j =>
    cases j with
    | zero => simpa [A,b,Pi.pow_apply] using! hf
    | succ j => simpa [Pi.pow_apply] using! hf

/-- North-pole contact amplitude of a canonical ordered pair in direction d. -/
def sphereChartContact (Q i j : ℕ) (R : ℝ) (d : ℂ) : ℂ :=
  sphereChartOrbital Q i R 0 * deriv (fun t : ℝ => sphereChartOrbital Q j R (t*d)) 0 -
  sphereChartOrbital Q j R 0 * deriv (fun t : ℝ => sphereChartOrbital Q i R (t*d)) 0

theorem sphereChartContact_apply (Q i j : ℕ) (hij : i < j) (R : ℝ) (d : ℂ) :
    sphereChartContact Q i j R d =
      if i=0 ∧ j=1 then
        (Real.sqrt (((Q+1:ℕ):ℝ)/(4*Real.pi*R^2)):ℂ) *
        ((Real.sqrt (((Q+1:ℕ):ℝ)*Q/(4*Real.pi*R^2)):ℂ)*(d/(2*R))) else 0 := by
  rw [sphereChartContact, (sphereChartOrbital_jet Q j R d).deriv, (sphereChartOrbital_jet Q i R d).deriv,
    sphereChartOrbital_origin, sphereChartOrbital_origin]
  have hj : j ≠ 0 := by omega
  by_cases hi : i=0 <;> by_cases h1 : j=1 <;> simp [hj,hi,h1]

theorem sphereChartContact_density (Q : ℕ) (R : ℝ) (hR : 0 < R) :
    ‖sphereChartContact Q 0 1 R 1‖^2 + ‖sphereChartContact Q 0 1 R Complex.I‖^2 =
      (Q:ℝ)*(Q+1)^2/(32*Real.pi^2*R^6) := by
  simp only [sphereChartContact_apply Q 0 1 (by decide), true_and, if_true, norm_mul, norm_div,
    Complex.norm_I, norm_one, Complex.norm_real, Real.norm_eq_abs, mul_pow, div_pow, sq_abs]
  rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  simp [abs_of_pos hR]
  field_simp
  ring

theorem sphereChartContact_normalized (n : ℕ) (R : ℝ) (hR : 0 < R) :
    (8*Real.pi*R^4*(2*(n:ℝ)+1)/(((n:ℝ)+1)*((n:ℝ)+2)^2)) *
      (‖sphereChartContact (n+1) 0 1 R 1‖^2 + ‖sphereChartContact (n+1) 0 1 R Complex.I‖^2) =
      (2*(n:ℝ)+1)/(4*Real.pi*R^2) := by
  rw [sphereChartContact_density _ R hR]
  push_cast
  field_simp [Real.pi_ne_zero, hR.ne']
  ring

end VortexGap.Fermion
