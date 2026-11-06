import VortexGap.Operator.LossDefect
noncomputable section
set_option autoImplicit false
namespace VortexGap
open scoped InnerProduct ComplexOrder
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem positive_energy_sqrt (A : H →L[ℂ] H) (hA : 0 ≤ A) (x : H) :
    (inner ℂ x (A x)).re = ‖CFC.sqrt A x‖^2 := by
  have hs : (CFC.sqrt A).adjoint = CFC.sqrt A :=
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg A)).star_eq
  have he : inner ℂ (CFC.sqrt A x) (CFC.sqrt A x) = inner ℂ x (A x) := by
    rw [← ContinuousLinearMap.adjoint_inner_right, hs]
    change inner ℂ x ((CFC.sqrt A * CFC.sqrt A) x) = _
    rw [CFC.sqrt_mul_sqrt_self A hA]
  rw [← he, ← RCLike.re_eq_complex_re, ← norm_sq_eq_re_inner (𝕜 := ℂ)]

theorem positive_energy_zero_iff (A : H →L[ℂ] H) (hA : 0 ≤ A) (x : H) :
    (inner ℂ x (A x)).re = 0 ↔ A x = 0 := by
  constructor
  · intro hz
    rw [positive_energy_sqrt A hA x] at hz
    have hx : CFC.sqrt A x = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hz)
    have he := congrArg (fun T : H →L[ℂ] H => T x) (CFC.sqrt_mul_sqrt_self A hA)
    simpa [mul_apply_eq_comp, hx] using he.symm
  · intro hx
    simp [hx]

/-- Two-sided positive form comparison identifies the full kernels without squaring
an operator inequality. The constants need not agree. -/
theorem positive_form_comparison_kernel
    (A B : H →L[ℂ] H) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (a b : ℝ) (ha : 0 < a)
    (hlo : ∀ x, a * (inner ℂ x (B x)).re ≤ (inner ℂ x (A x)).re)
    (hhi : ∀ x, (inner ℂ x (A x)).re ≤ b * (inner ℂ x (B x)).re) :
    LinearMap.ker A.toLinearMap = LinearMap.ker B.toLinearMap := by
  ext x
  change A x = 0 ↔ B x = 0
  constructor
  · intro hx
    apply (positive_energy_zero_iff B hB x).mp
    have hn := (ContinuousLinearMap.nonneg_iff_isPositive.mp hB).re_inner_nonneg_right x
    change 0 ≤ (inner ℂ x (B x)).re at hn
    have hh := hlo x
    simp only [hx, inner_zero_right, Complex.zero_re] at hh
    nlinarith
  · intro hx
    apply (positive_energy_zero_iff A hA x).mp
    have hn := (ContinuousLinearMap.nonneg_iff_isPositive.mp hA).re_inner_nonneg_right x
    change 0 ≤ (inner ℂ x (A x)).re at hn
    have hh := hhi x
    simp only [hx, inner_zero_right, Complex.zero_re, mul_zero] at hh
    exact le_antisymm hh hn

/-- The reference energy bound is used on the common kernel complement;
no implication from A >= a B to A^2 >= a^2 B^2 is used. -/
theorem positive_form_comparison_gap
    (A B : H →L[ℂ] H) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (a b γ : ℝ) (ha : 0 < a)
    (hlo : ∀ x, a * (inner ℂ x (B x)).re ≤ (inner ℂ x (A x)).re)
    (hhi : ∀ x, (inner ℂ x (A x)).re ≤ b * (inner ℂ x (B x)).re)
    (hgap : ∀ x ∈ (LinearMap.ker B.toLinearMap)ᗮ,
      γ * ‖x‖^2 ≤ (inner ℂ x (B x)).re) :
    ∀ x ∈ (LinearMap.ker A.toLinearMap)ᗮ,
      (a*γ) * ‖x‖^2 ≤ (inner ℂ x (A x)).re := by
  intro x hx
  rw [positive_form_comparison_kernel A B hA hB a b ha hlo hhi] at hx
  have h := mul_le_mul_of_nonneg_left (hgap x hx) ha.le
  calc
    (a*γ)*‖x‖^2 = a*(γ*‖x‖^2) := by ring
    _ ≤ a*(inner ℂ x (B x)).re := h
    _ ≤ (inner ℂ x (A x)).re := hlo x

end VortexGap



