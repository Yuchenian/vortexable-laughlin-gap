import VortexGap.Fermion.CountablePairLiftCompatibility
import Mathlib.Analysis.Normed.Group.Tannery

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open Filter
open scoped Topology

theorem countablePairAmplify_difference_norm_sq
    (Q R : CountablePairSpace →L[ℂ] CountablePairSpace) (z : CountablePairStackSpace) :
    ‖countablePairAmplify Q z - countablePairAmplify R z‖ ^ 2 =
      ∑' A, ‖Q (countablePairFiber z A) - R (countablePairFiber z A)‖ ^ 2 := by
  rw [countablePairStackSpace_norm_sq]
  apply tsum_congr
  intro A
  rfl

/-- Uniformly bounded strong limits survive the concrete spectator amplification. -/
theorem countablePairAmplify_tendsto {ι : Type*} {l : Filter ι}
    (Q : ι → CountablePairSpace →L[ℂ] CountablePairSpace)
    (R : CountablePairSpace →L[ℂ] CountablePairSpace)
    (K : ℝ) (hK : 0 ≤ K) (hbound : ∀ i, ‖Q i‖ ≤ K)
    (hstrong : ∀ p, Tendsto (fun i => Q i p) l (𝓝 (R p)))
    (z : CountablePairStackSpace) :
    Tendsto (fun i => countablePairAmplify (Q i) z) l (𝓝 (countablePairAmplify R z)) := by
  have hs : Summable (fun A => (K + ‖R‖)^2 * ‖countablePairFiber z A‖^2) :=
    (l2_norm_sq_summable (l2Exchange CountablePairIndex (Finset ℕ) z)).mul_left _
  have hp (A : Finset ℕ) : Tendsto
      (fun i => ‖Q i (countablePairFiber z A) - R (countablePairFiber z A)‖^2) l (𝓝 (0 : ℝ)) := by
    have hc : Tendsto (fun _ : ι => R (countablePairFiber z A)) l
        (𝓝 (R (countablePairFiber z A))) := tendsto_const_nhds
    simpa using ((hstrong (countablePairFiber z A)).sub hc).norm.pow 2
  have hb : ∀ᶠ i in l, ∀ A : Finset ℕ,
      ‖‖Q i (countablePairFiber z A) - R (countablePairFiber z A)‖^2‖ ≤
        (K + ‖R‖)^2 * ‖countablePairFiber z A‖^2 := by
    apply Eventually.of_forall
    intro i A
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hn : ‖Q i (countablePairFiber z A) - R (countablePairFiber z A)‖ ≤
        (K + ‖R‖) * ‖countablePairFiber z A‖ := by
      calc
        _ ≤ ‖Q i (countablePairFiber z A)‖ + ‖R (countablePairFiber z A)‖ := norm_sub_le _ _
        _ ≤ K * ‖countablePairFiber z A‖ + ‖R‖ * ‖countablePairFiber z A‖ :=
          add_le_add ((Q i).le_of_opNorm_le (hbound i) _) (R.le_opNorm _)
        _ = _ := by ring
    calc
      _ ≤ ((K + ‖R‖) * ‖countablePairFiber z A‖)^2 :=
        (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (add_nonneg hK (norm_nonneg _)) (norm_nonneg _))).mpr hn
      _ = _ := mul_pow _ _ 2
  have ht := tendsto_tsum_of_dominated_convergence hs hp hb
  have hsq : Tendsto (fun i => ‖countablePairAmplify (Q i) z - countablePairAmplify R z‖^2)
      l (𝓝 (0 : ℝ)) := by
    simpa only [countablePairAmplify_difference_norm_sq, tsum_zero] using ht
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have h := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hsq
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using h

theorem countablePairLift_uniform_bound (N : ℕ) {ι : Type*}
    (Q : ι → CountablePairSpace →L[ℂ] CountablePairSpace) (K : ℝ)
    (hbound : ∀ i, ‖Q i‖ ≤ K) (i : ι) :
    ‖countablePairLift N (Q i)‖ ≤ (N.choose 2 : ℝ) * K :=
  (countablePairLift_opNorm_le N _).trans
    (mul_le_mul_of_nonneg_left (hbound i) (Nat.cast_nonneg _))

theorem countablePairLift_norm_sub_le (N : ℕ)
    (Q R : CountablePairSpace →L[ℂ] CountablePairSpace) :
    ‖countablePairLift N Q - countablePairLift N R‖ ≤ (N.choose 2 : ℝ) * ‖Q - R‖ := by
  rw [← countablePairLift_sub]
  exact countablePairLift_opNorm_le N _

/-- Strong convergence here transfers operators, never a spectral gap of their cutoffs. -/
theorem countablePairLift_tendsto (N : ℕ) {ι : Type*} {l : Filter ι}
    (Q : ι → CountablePairSpace →L[ℂ] CountablePairSpace)
    (R : CountablePairSpace →L[ℂ] CountablePairSpace)
    (K : ℝ) (hK : 0 ≤ K) (hbound : ∀ i, ‖Q i‖ ≤ K)
    (hstrong : ∀ p, Tendsto (fun i => Q i p) l (𝓝 (R p)))
    (x : countableSector N) :
    Tendsto (fun i => countablePairLift N (Q i) x) l (𝓝 (countablePairLift N R x)) := by
  exact ((countablePairStack N).adjoint.continuous.tendsto
    (countablePairAmplify R (countablePairStack N x))).comp
      (countablePairAmplify_tendsto Q R K hK hbound hstrong (countablePairStack N x))

end VortexGap.Fermion
