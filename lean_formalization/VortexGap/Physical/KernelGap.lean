import VortexGap.Physical.FormComparison
import VortexGap.Operator.QuadraticNorm
noncomputable section
set_option autoImplicit false
namespace VortexGap
open scoped InnerProduct ComplexOrder
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem positive_sqrt_kernel (A : H →L[ℂ] H) (hA : 0 ≤ A) :
    (CFC.sqrt A).toLinearMap.ker = A.toLinearMap.ker := by
  ext x
  change CFC.sqrt A x = 0 ↔ A x = 0
  rw [← positive_energy_zero_iff A hA x, positive_energy_sqrt A hA x]
  simp only [sq_eq_zero_iff, norm_eq_zero]

theorem quadratic_gap_on_sqrt_range (A : H →L[ℂ] H) (hA : 0 ≤ A) (γ : ℝ)
    (hg : (A*A-(γ : ℂ) • A).IsPositive) (y : H) :
    γ * ‖CFC.sqrt A y‖^2 ≤ (inner ℂ (CFC.sqrt A y) (A (CFC.sqrt A y))).re := by
  have h := (quadratic_positive_norm_iff A (ContinuousLinearMap.nonneg_iff_isPositive.mp hA) γ).mp hg y
  rw [positive_energy_sqrt A hA y] at h
  rw [positive_energy_sqrt A hA]
  have hs : CFC.sqrt A (CFC.sqrt A y) = A y :=
    congrArg (fun T : H →L[ℂ] H => T y) (CFC.sqrt_mul_sqrt_self A hA)
  rw [hs]
  exact h

/-- Extend the range estimate by continuity to the whole kernel complement.
No discrete-spectrum assumption or inverse on the full Hilbert space is used. -/
theorem quadratic_gap_on_kernel_complement (A : H →L[ℂ] H) (hA : 0 ≤ A) (γ : ℝ)
    (hg : (A*A-(γ : ℂ) • A).IsPositive) :
    ∀ x ∈ (LinearMap.ker A.toLinearMap)ᗮ,
      γ * ‖x‖^2 ≤ (inner ℂ x (A x)).re := by
  have hs : (CFC.sqrt A).adjoint = CFC.sqrt A :=
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg A)).star_eq
  have hr : (LinearMap.ker A.toLinearMap)ᗮ =
      (CFC.sqrt A).toLinearMap.range.topologicalClosure := by
    rw [← positive_sqrt_kernel A hA, ContinuousLinearMap.orthogonal_ker, hs]
  have hc : IsClosed {x : H | γ * ‖x‖^2 ≤ (inner ℂ x (A x)).re} :=
    isClosed_le (by fun_prop) (by fun_prop)
  intro x hx
  rw [hr] at hx
  change x ∈ closure (Set.range (fun y : H => CFC.sqrt A y)) at hx
  apply closure_minimal (s := Set.range (fun y : H => CFC.sqrt A y)) ?_ hc hx
  rintro z ⟨y, rfl⟩
  exact quadratic_gap_on_sqrt_range A hA γ hg y

/-- Physical form comparison now takes the original quadratic reference gap,
not a separately assumed bound on a complement. -/
theorem positive_form_comparison_of_quadratic_gap
    (A B : H →L[ℂ] H) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (a b γ : ℝ) (ha : 0 < a)
    (hlo : ∀ x, a * (inner ℂ x (B x)).re ≤ (inner ℂ x (A x)).re)
    (hhi : ∀ x, (inner ℂ x (A x)).re ≤ b * (inner ℂ x (B x)).re)
    (hgap : (B*B-(γ : ℂ) • B).IsPositive) :
    ∀ x ∈ (LinearMap.ker A.toLinearMap)ᗮ,
      (a*γ) * ‖x‖^2 ≤ (inner ℂ x (A x)).re :=
  positive_form_comparison_gap A B hA hB a b γ ha hlo hhi
    (quadratic_gap_on_kernel_complement B hB γ hgap)

end VortexGap

