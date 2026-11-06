import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Tactic
noncomputable section
set_option autoImplicit false
namespace VortexGap
open scoped InnerProduct
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Quadratic operator positivity is equivalent to the norm inequality for every
vector of the complete Hilbert space, not merely for eigenvectors. -/
theorem quadratic_positive_norm_iff (T : H →L[ℂ] H) (hT : T.IsPositive) (γ : ℝ) :
    (T*T - (γ : ℂ) • T).IsPositive ↔
      ∀ x, γ * (inner ℂ x (T x)).re ≤ ‖T x‖^2 := by
  have hr (x : H) : ((inner ℂ x (T x)).re : ℂ) = inner ℂ x (T x) := by
    have h := (ContinuousLinearMap.isPositive_iff_complex T).mp hT x
    simpa only [hT.inner_left_eq_inner_right, RCLike.re_eq_complex_re] using h.1
  have hi (x : H) : inner ℂ ((T*T - (γ : ℂ) • T) x) x =
      ((‖T x‖^2 - γ * (inner ℂ x (T x)).re : ℝ) : ℂ) := by
    simp only [sub_apply, ContinuousLinearMap.mul_apply, smul_apply,
      inner_sub_left, inner_smul_left, Complex.conj_ofReal]
    rw [hT.inner_left_eq_inner_right (T x) x, inner_self_eq_norm_sq_to_K,
      hT.inner_left_eq_inner_right x x, ← hr x, ← RCLike.ofReal_pow]
    push_cast
    rfl
  rw [ContinuousLinearMap.isPositive_iff_complex]
  simp only [hi, RCLike.re_eq_complex_re, Complex.ofReal_re, true_and, sub_nonneg]
end VortexGap
