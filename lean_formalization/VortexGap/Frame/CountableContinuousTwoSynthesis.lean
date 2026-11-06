import VortexGap.Frame.CountableContinuousPairStack
import VortexGap.Frame.CountableTwoNoise

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory Filter
open scoped InnerProduct ENNReal Topology ComplexOrder

/-- The actual two-environment exterior filter and Fock embedding. -/
def countablePairLossOutput (M : CountableOrbital →L[ℂ] CountableOrbital) :
    CountablePairStackSpace →L[ℂ] CountableSpace :=
  countablePairEnvironmentEmbed.comp
    (countablePairAmplify (countablePairFilter (lossDefect M) (lossDefect_nonneg M)))

theorem countablePairLossOutput_norm_sq
    (M : CountableOrbital →L[ℂ] CountableOrbital) (hM : 0 ≤ M) (hMc : ‖M‖ ≤ 1)
    (z : CountablePairStackSpace) :
    ‖countablePairLossOutput M z‖^2 ≤ ‖1-M^2‖^2 * ‖z‖^2 :=
  countablePairEnvironment_filter_norm_sq M hM hMc z

theorem countablePairLossOutput_wedge
    (M : CountableOrbital →L[ℂ] CountableOrbital) (u v : CountableOrbital) (x : CountableSpace) :
    countablePairLossOutput M (countablePairTensor (countableWedge u v) x) =
      countableLossCreationTwo M u v x :=
  (countableLossCreationTwo_factorization M u v x).symm

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) (p : α → CountablePairSpace)
  (hp : ∀ q, MemLp (fun a => inner ℂ (p a) q) 2 μ)
  (β : ℝ) (hβ : 0 ≤ β)
  (hb : ∀ q, (∫ a, ‖inner ℂ (p a) q‖^2 ∂μ) ≤ β * ‖q‖^2)
  (s : ℕ → Set α) (hc : AECover μ atTop s)
  (hloc : ∀ n, MemLp p 2 (μ.restrict (s n)))
  (M : CountableOrbital →L[ℂ] CountableOrbital)

/-- Global creation synthesis into the actual doubled Fock space. -/
def countableContinuousTwoSynthesis : Lp CountableSpace 2 μ →L[ℂ] CountableSpace :=
  (countablePairLossOutput M).comp
    (countableContinuousPairStackSynthesis μ p hp β hβ hb s hc hloc)

theorem countableContinuousTwoSynthesis_norm_sq (hM : 0 ≤ M) (hMc : ‖M‖ ≤ 1)
    (f : Lp CountableSpace 2 μ) :
    ‖countableContinuousTwoSynthesis μ p hp β hβ hb s hc hloc M f‖^2 ≤
      β * ‖1-M^2‖^2 * ‖f‖^2 := by
  change ‖countablePairLossOutput M
    (countableContinuousPairStackSynthesis μ p hp β hβ hb s hc hloc f)‖^2 ≤ _
  calc
    _ ≤ ‖1-M^2‖^2 * ‖countableContinuousPairStackSynthesis μ p hp β hβ hb s hc hloc f‖^2 :=
      countablePairLossOutput_norm_sq M hM hMc _
    _ ≤ ‖1-M^2‖^2 * (β * ‖f‖^2) := mul_le_mul_of_nonneg_left
      (countableContinuousPairStackSynthesis_norm_sq μ p hp β hβ hb s hc hloc f) (sq_nonneg _)
    _ = _ := by ring

include hloc in
theorem countablePairLossOutput_local_integrable (n : ℕ) (f : Lp CountableSpace 2 μ) :
    Integrable (fun a => countablePairLossOutput M (countablePairTensor (p a) (f a)))
      (μ.restrict (s n)) :=
  (countablePairLossOutput M).integrable_comp
    (countablePairTensor_local_integrable μ p s hloc n f)

theorem countableContinuousTwoSynthesis_cutoff (n : ℕ) (f : Lp CountableSpace 2 μ) :
    countableContinuousTwoSynthesis μ p hp β hβ hb s hc hloc M
      (Frame.l2Cutoff μ (s n) (hc.measurableSet n) f) =
      ∫ a in s n, countablePairLossOutput M (countablePairTensor (p a) (f a)) ∂μ := by
  change countablePairLossOutput M (countableContinuousPairStackSynthesis μ p hp β hβ hb s hc hloc
    (Frame.l2Cutoff μ (s n) (hc.measurableSet n) f)) = _
  rw [countableContinuousPairStackSynthesis_cutoff,
    ← (countablePairLossOutput M).integral_comp_comm
      (countablePairTensor_local_integrable μ p s hloc n f)]

theorem countableContinuousTwoSynthesis_integral_tendsto
    (hm : Monotone s) (hu : ⋃ n, s n = Set.univ) (f : Lp CountableSpace 2 μ) :
    Tendsto (fun n => ∫ a in s n,
      countablePairLossOutput M (countablePairTensor (p a) (f a)) ∂μ) atTop
      (𝓝 (countableContinuousTwoSynthesis μ p hp β hβ hb s hc hloc M f)) := by
  have h := ((countableContinuousTwoSynthesis μ p hp β hβ hb s hc hloc M).continuous.tendsto f).comp
    (Frame.l2Cutoff_tendsto μ s hc.measurableSet hm hu f)
  have he (n : ℕ) := countableContinuousTwoSynthesis_cutoff μ p hp β hβ hb s hc hloc M n f
  simpa only [Function.comp_def, he] using h

theorem countableContinuousTwoSynthesis_wedge_cutoff
    (u v : α → CountableOrbital) (hpw : ∀ a, p a = countableWedge (u a) (v a))
    (n : ℕ) (f : Lp CountableSpace 2 μ) :
    countableContinuousTwoSynthesis μ p hp β hβ hb s hc hloc M
      (Frame.l2Cutoff μ (s n) (hc.measurableSet n) f) =
      ∫ a in s n, countableLossCreationTwo M (u a) (v a) (f a) ∂μ := by
  rw [countableContinuousTwoSynthesis_cutoff]
  apply integral_congr_ae
  exact Eventually.of_forall fun a => by
    change countablePairLossOutput M (countablePairTensor (p a) (f a)) = _
    rw [hpw, countablePairLossOutput_wedge]

end VortexGap.Fermion
