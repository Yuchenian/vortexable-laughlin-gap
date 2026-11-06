import VortexGap.Operator.L2Amplification
import Mathlib.Analysis.Normed.Group.Tannery

noncomputable section
set_option autoImplicit false
namespace VortexGap
open Filter
open scoped Topology

theorem l2Amplify_difference_norm_sq (α : Type*) {β : Type*}
    (Q R : lp (fun _ : β => ℂ) 2 →L[ℂ] lp (fun _ : β => ℂ) 2) (z : L2Product α β) :
    ‖l2Amplify α Q z - l2Amplify α R z‖ ^ 2 =
      ∑' A, ‖Q (l2ProductFiber z A) - R (l2ProductFiber z A)‖ ^ 2 := by
  rw [l2Product_norm_sq]
  apply tsum_congr
  intro A
  have hf : l2ProductFiber (l2Amplify α Q z - l2Amplify α R z) A =
      Q (l2ProductFiber z A) - R (l2ProductFiber z A) := by ext b; rfl
  rw [hf]

/-- Uniformly bounded strong limits survive the concrete spectator amplification. -/
theorem l2Amplify_tendsto (α : Type*) {β : Type*} {ι : Type*} {l : Filter ι}
    (Q : ι → lp (fun _ : β => ℂ) 2 →L[ℂ] lp (fun _ : β => ℂ) 2)
    (R : lp (fun _ : β => ℂ) 2 →L[ℂ] lp (fun _ : β => ℂ) 2)
    (K : ℝ) (hK : 0 ≤ K) (hbound : ∀ i, ‖Q i‖ ≤ K)
    (hstrong : ∀ p, Tendsto (fun i => Q i p) l (𝓝 (R p)))
    (z : L2Product α β) :
    Tendsto (fun i => l2Amplify α (Q i) z) l (𝓝 (l2Amplify α R z)) := by
  have hs : Summable (fun A => (K + ‖R‖)^2 * ‖l2ProductFiber z A‖^2) :=
    (l2_norm_sq_summable (l2Curry α β z)).mul_left _
  have hp (A : α) : Tendsto
      (fun i => ‖Q i (l2ProductFiber z A) - R (l2ProductFiber z A)‖^2) l (𝓝 (0 : ℝ)) := by
    have hc : Tendsto (fun _ : ι => R (l2ProductFiber z A)) l
        (𝓝 (R (l2ProductFiber z A))) := tendsto_const_nhds
    simpa using ((hstrong (l2ProductFiber z A)).sub hc).norm.pow 2
  have hb : ∀ᶠ i in l, ∀ A : α,
      ‖‖Q i (l2ProductFiber z A) - R (l2ProductFiber z A)‖^2‖ ≤
        (K + ‖R‖)^2 * ‖l2ProductFiber z A‖^2 := by
    apply Eventually.of_forall
    intro i A
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hn : ‖Q i (l2ProductFiber z A) - R (l2ProductFiber z A)‖ ≤
        (K + ‖R‖) * ‖l2ProductFiber z A‖ := by
      calc
        _ ≤ ‖Q i (l2ProductFiber z A)‖ + ‖R (l2ProductFiber z A)‖ := norm_sub_le _ _
        _ ≤ K * ‖l2ProductFiber z A‖ + ‖R‖ * ‖l2ProductFiber z A‖ :=
          add_le_add ((Q i).le_of_opNorm_le (hbound i) _) (R.le_opNorm _)
        _ = _ := by ring
    calc
      _ ≤ ((K + ‖R‖) * ‖l2ProductFiber z A‖)^2 :=
        (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (add_nonneg hK (norm_nonneg _)) (norm_nonneg _))).mpr hn
      _ = _ := mul_pow _ _ 2
  have ht := tendsto_tsum_of_dominated_convergence hs hp hb
  have hsq : Tendsto (fun i => ‖l2Amplify α (Q i) z - l2Amplify α R z‖^2)
      l (𝓝 (0 : ℝ)) := by
    simpa only [l2Amplify_difference_norm_sq, tsum_zero] using ht
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have h := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hsq
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using h

end VortexGap
