import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Adjoint

set_option autoImplicit false
namespace VortexGap.Frame
open scoped BigOperators

/-- Scalar unweighted finite Schur estimate. This is not yet the operator-valued
two-frame estimate, and makes no assertion about the physical constant 14. -/
theorem finite_schur_quadratic {ι : Type*} [Fintype ι]
    (k : ι → ι → ℝ) (C : ℝ)
    (hk : ∀ i j, 0 ≤ k i j) (hs : ∀ i j, k i j = k j i)
    (hr : ∀ i, ∑ j, k i j ≤ C) (u : ι → ℝ) :
    ∑ i, ∑ j, k i j * u i * u j ≤ C * ∑ i, (u i)^2 := by
  have hcol : (∑ i, ∑ j, k i j * (u j)^2) = ∑ i, ∑ j, k i j * (u i)^2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hs j i]
  have hrow : (∑ i, ∑ j, k i j * (u i)^2) ≤ C * ∑ i, (u i)^2 := by
    calc
      _ = ∑ i, (∑ j, k i j) * (u i)^2 := by simp_rw [Finset.sum_mul]
      _ ≤ ∑ i, C * (u i)^2 := by
        exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hr i) (sq_nonneg _)
      _ = _ := by rw [Finset.mul_sum]
  have hp : 0 ≤ ∑ i, ∑ j, k i j * (u i - u j)^2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (hk i j) (sq_nonneg _)
  have he : (∑ i, ∑ j, k i j * (u i - u j)^2) =
      (∑ i, ∑ j, k i j * (u i)^2) + (∑ i, ∑ j, k i j * (u j)^2) -
        2 * (∑ i, ∑ j, k i j * u i * u j) := by
    have term (i j : ι) : k i j * (u i - u j)^2 =
        k i j * (u i)^2 + k i j * (u j)^2 - 2 * (k i j * u i * u j) := by ring
    simp_rw [term, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [he, hcol] at hp
  linarith

/-- The operator-valued unweighted finite Schur step. The Gram majorant is an
explicit input here; the concrete two-frame trace-norm bound remains separate. -/
theorem finite_synthesis_norm_sq {ι E F : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (R : ι → E →L[ℂ] F) (k : ι → ι → ℝ) (C : ℝ)
    (hk : ∀ i j, 0 ≤ k i j) (hs : ∀ i j, k i j = k j i)
    (hr : ∀ i, ∑ j, k i j ≤ C)
    (hGram : ∀ i j, ‖(R i).adjoint ∘L R j‖ ≤ k i j) (f : ι → E) :
    ‖∑ i, R i (f i)‖ ^ 2 ≤ C * ∑ i, ‖f i‖ ^ 2 := by
  have hterm (i j : ι) :
      (inner ℂ (R i (f i)) (R j (f j))).re ≤ k i j * ‖f i‖ * ‖f j‖ := by
    rw [← ContinuousLinearMap.adjoint_inner_right (R i)]
    calc
      _ ≤ ‖inner ℂ (f i) ((R i).adjoint (R j (f j)))‖ := RCLike.re_le_norm _
      _ ≤ ‖f i‖ * ‖((R i).adjoint ∘L R j) (f j)‖ := norm_inner_le_norm _ _
      _ ≤ ‖f i‖ * (‖(R i).adjoint ∘L R j‖ * ‖f j‖) :=
        mul_le_mul_of_nonneg_left (((R i).adjoint ∘L R j).le_opNorm (f j)) (norm_nonneg _)
      _ ≤ ‖f i‖ * (k i j * ‖f j‖) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (hGram i j) (norm_nonneg _)) (norm_nonneg _)
      _ = _ := by ring
  have he : ‖∑ i, R i (f i)‖ ^ 2 =
      ∑ i, ∑ j, (inner ℂ (R i (f i)) (R j (f j))).re := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
    simp only [sum_inner, inner_sum, map_sum]
    rw [Finset.sum_comm]
    rfl
  calc
    _ = _ := he
    _ ≤ ∑ i, ∑ j, k i j * ‖f i‖ * ‖f j‖ :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
    _ ≤ _ := finite_schur_quadratic k C hk hs hr (fun i => ‖f i‖)

end VortexGap.Frame
