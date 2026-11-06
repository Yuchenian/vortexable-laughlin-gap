import VortexGap.Fermion.CountablePairLiftCovariance
import VortexGap.Fermion.CountablePairLimits
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open Filter
open scoped InnerProduct BigOperators ENNReal Topology

def countablePairTruncate (s : Finset CountablePairIndex) :
    CountablePairSpace →L[ℂ] CountablePairSpace :=
  ∑ a ∈ s, InnerProductSpace.rankOne ℂ (lp.single 2 a 1) (lp.single 2 a 1)

theorem countablePairTruncate_apply (s : Finset CountablePairIndex) (p : CountablePairSpace) :
    countablePairTruncate s p = ∑ a ∈ s, lp.single 2 a (p a) := by
  simp [countablePairTruncate, InnerProductSpace.rankOne_apply, lp.inner_single_left,
    RCLike.inner_apply, ← lp.single_smul]

theorem countablePairTruncate_norm_le (s : Finset CountablePairIndex) (p : CountablePairSpace) :
    ‖countablePairTruncate s p‖ ≤ ‖p‖ := by
  have hs : Summable (fun a => ‖p a‖^2) := by
    simpa using (lp.memℓp p).summable (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)
  have hn : ‖p‖^2 = ∑' a, ‖p a‖^2 := by
    simpa using lp.norm_rpow_eq_tsum (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal) p
  have ht : ‖countablePairTruncate s p‖^2 = ∑ a ∈ s, ‖p a‖^2 := by
    rw [countablePairTruncate_apply]
    simpa using lp.norm_sum_single (p := (2 : ℝ≥0∞)) (by norm_num) (fun a => p a) s
  have h := hs.sum_le_tsum s (fun a _ => sq_nonneg ‖p a‖)
  rw [← ht, ← hn] at h
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

theorem countablePairTruncate_tendsto (p : CountablePairSpace) :
    Tendsto (fun s => countablePairTruncate s p) atTop (𝓝 p) := by
  simpa only [countablePairTruncate_apply, HasSum, SummationFilter.unconditional_filter]
    using lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) p

theorem countablePairTruncate_comp_rankOne
    (Q : CountablePairSpace →L[ℂ] CountablePairSpace) (s : Finset CountablePairIndex) :
    Q.comp (countablePairTruncate s) =
      ∑ a ∈ s, InnerProductSpace.rankOne ℂ (Q (lp.single 2 a 1)) (lp.single 2 a 1) := by
  ext p
  simp [countablePairTruncate, InnerProductSpace.rankOne_apply, map_sum, map_smul]

theorem countablePairTruncate_comp_bound
    (Q : CountablePairSpace →L[ℂ] CountablePairSpace) (s : Finset CountablePairIndex) :
    ‖Q.comp (countablePairTruncate s)‖ ≤ ‖Q‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun p =>
    (Q.le_opNorm _).trans (mul_le_mul_of_nonneg_left
      (countablePairTruncate_norm_le s p) (norm_nonneg Q)))

theorem countablePairTruncate_comp_tendsto
    (Q : CountablePairSpace →L[ℂ] CountablePairSpace) (p : CountablePairSpace) :
    Tendsto (fun s => Q.comp (countablePairTruncate s) p) atTop (𝓝 (Q p)) :=
  Q.continuous.continuousAt.tendsto.comp (countablePairTruncate_tendsto p)
end VortexGap.Fermion
