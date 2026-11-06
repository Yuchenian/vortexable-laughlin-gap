import VortexGap.Frame.CountableContinuousTwoSynthesis
import VortexGap.Frame.CountableFilteredEnergy

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory Filter
open scoped InnerProduct ENNReal Topology ComplexOrder
variable {α : Type*} [MeasurableSpace α] (μ : Measure α) (p : α → CountablePairSpace)
  (hp : ∀ q, MemLp (fun a => inner ℂ (p a) q) 2 μ)
  (β : ℝ) (hβ : 0 ≤ β)
  (hb : ∀ q, (∫ a, ‖inner ℂ (p a) q‖^2 ∂μ) ≤ β * ‖q‖^2)
  (s : ℕ → Set α) (hc : AECover μ atTop s)
  (hloc : ∀ n, MemLp p 2 (μ.restrict (s n)))
  (M : CountableOrbital →L[ℂ] CountableOrbital) (hM : 0 ≤ M) (hMc : ‖M‖ ≤ 1)

/-- The global analysis of the actual exterior-square filtered annihilation field. -/
def countableContinuousFilteredAnalysis (N : ℕ) : countableSector N →L[ℂ] Lp CountableSpace 2 μ :=
  countableContinuousFrameAnalysis μ (fun a => countablePairFilter M hM (p a))
    (countableFilteredPair_coeff_memLp μ p hp (countablePairFilter M hM)) β hβ
    (countableFilteredPair_bessel μ p β hβ hb _ (countablePairFilter_contract M hM hMc))
    s hc (fun n => countableFilteredPair_local_memLp μ p _ (s n) (hloc n)) N

theorem countableContinuousFilteredAnalysis_ae (N : ℕ) (x : countableSector N) :
    countableContinuousFilteredAnalysis μ p hp β hβ hb s hc hloc M hM hMc N x =ᵐ[μ]
      fun a => countablePairAnnihilate N (countablePairFilter M hM (p a)) x :=
  countableContinuousFrameAnalysis_ae μ _ _ _ _ _ _ _ _ N x

theorem countableContinuousFilteredAnalysis_norm_sq
    (hm : Monotone s) (hu : ⋃ n, s n = Set.univ) (N : ℕ) (x : countableSector N) :
    ‖countableContinuousFilteredAnalysis μ p hp β hβ hb s hc hloc M hM hMc N x‖^2 =
      (inner ℂ x (countablePairLift N ((countablePairFilter M hM).comp
        ((countableContinuousPairOperator μ p hp β hβ hb).comp (countablePairFilter M hM).adjoint))
        x)).re := by
  change ‖countableContinuousFrameAnalysis μ _ _ _ _ _ _ _ _ N x‖^2 = _
  rw [countableContinuousFrameAnalysis, Frame.besselAnalysis_norm_sq]
  exact countableLossFilteredFrame_energy μ p hp β hβ hb s hc hloc hm hu M hM hMc N x

/-- The actual two-environment output, with the filtered annihilation analysis as input. -/
def countableContinuousNoiseTwo (N : ℕ) : countableSector N →L[ℂ] CountableSpace :=
  (countableContinuousTwoSynthesis μ p hp β hβ hb s hc hloc M).comp
    (countableContinuousFilteredAnalysis μ p hp β hβ hb s hc hloc M hM hMc N)

theorem countableContinuousNoiseTwo_relative
    (hm : Monotone s) (hu : ⋃ n, s n = Set.univ) (N : ℕ) (x : countableSector N) :
    ‖countableContinuousNoiseTwo μ p hp β hβ hb s hc hloc M hM hMc N x‖^2 ≤
      β * ‖1-M^2‖^2 * (inner ℂ x (countablePairLift N ((countablePairFilter M hM).comp
        ((countableContinuousPairOperator μ p hp β hβ hb).comp (countablePairFilter M hM).adjoint))
        x)).re := by
  have h := countableContinuousTwoSynthesis_norm_sq μ p hp β hβ hb s hc hloc M hM hMc
    (countableContinuousFilteredAnalysis μ p hp β hβ hb s hc hloc M hM hMc N x)
  rw [countableContinuousFilteredAnalysis_norm_sq μ p hp β hβ hb s hc hloc M hM hMc hm hu N x] at h
  exact h

theorem countableContinuousNoiseTwo_cutoff (N : ℕ) (x : countableSector N) (n : ℕ) :
    countableContinuousTwoSynthesis μ p hp β hβ hb s hc hloc M
      (Frame.l2Cutoff μ (s n) (hc.measurableSet n)
        (countableContinuousFilteredAnalysis μ p hp β hβ hb s hc hloc M hM hMc N x)) =
      ∫ a in s n, countablePairLossOutput M (countablePairTensor (p a)
        (countablePairAnnihilate N (countablePairFilter M hM (p a)) x)) ∂μ := by
  rw [countableContinuousTwoSynthesis_cutoff]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae
    (countableContinuousFilteredAnalysis_ae μ p hp β hβ hb s hc hloc M hM hMc N x)] with a ha
  rw [ha]

include hp hβ hb hc hloc hMc in
theorem countableContinuousNoiseTwo_local_integrable (N : ℕ) (x : countableSector N) (n : ℕ) :
    Integrable (fun a => countablePairLossOutput M (countablePairTensor (p a)
      (countablePairAnnihilate N (countablePairFilter M hM (p a)) x))) (μ.restrict (s n)) := by
  have h := countablePairLossOutput_local_integrable μ p s hloc M n
    (countableContinuousFilteredAnalysis μ p hp β hβ hb s hc hloc M hM hMc N x)
  apply h.congr
  filter_upwards [ae_restrict_of_ae
    (countableContinuousFilteredAnalysis_ae μ p hp β hβ hb s hc hloc M hM hMc N x)] with a ha
  rw [ha]

theorem countableContinuousNoiseTwo_integral_tendsto
    (hm : Monotone s) (hu : ⋃ n, s n = Set.univ) (N : ℕ) (x : countableSector N) :
    Tendsto (fun n => ∫ a in s n, countablePairLossOutput M (countablePairTensor (p a)
      (countablePairAnnihilate N (countablePairFilter M hM (p a)) x)) ∂μ) atTop
      (𝓝 (countableContinuousNoiseTwo μ p hp β hβ hb s hc hloc M hM hMc N x)) := by
  have h := ((countableContinuousTwoSynthesis μ p hp β hβ hb s hc hloc M).continuous.tendsto
    (countableContinuousFilteredAnalysis μ p hp β hβ hb s hc hloc M hM hMc N x)).comp
    (Frame.l2Cutoff_tendsto μ s hc.measurableSet hm hu _)
  have he (n : ℕ) := countableContinuousNoiseTwo_cutoff μ p hp β hβ hb s hc hloc M hM hMc N x n
  simpa only [Function.comp_def, he, countableContinuousNoiseTwo,
    ContinuousLinearMap.comp_apply] using h

theorem countableContinuousNoiseTwo_wedge_cutoff
    (u v : α → CountableOrbital) (hpw : ∀ a, p a = countableWedge (u a) (v a))
    (N : ℕ) (x : countableSector N) (n : ℕ) :
    countableContinuousTwoSynthesis μ p hp β hβ hb s hc hloc M
      (Frame.l2Cutoff μ (s n) (hc.measurableSet n)
        (countableContinuousFilteredAnalysis μ p hp β hβ hb s hc hloc M hM hMc N x)) =
      ∫ a in s n, countableLossCreationTwo M (u a) (v a)
        (countablePairAnnihilate N (countableWedge (M (u a)) (M (v a))) x) ∂μ := by
  rw [countableContinuousNoiseTwo_cutoff]
  apply integral_congr_ae
  exact Eventually.of_forall fun a => by
    change countablePairLossOutput M (countablePairTensor (p a)
      (countablePairAnnihilate N (countablePairFilter M hM (p a)) x)) = _
    rw [hpw, countablePairFilter_wedge, countablePairLossOutput_wedge]

theorem countableContinuousNoiseTwo_wedge_integral_tendsto
    (hm : Monotone s) (hu : ⋃ n, s n = Set.univ)
    (u v : α → CountableOrbital) (hpw : ∀ a, p a = countableWedge (u a) (v a))
    (N : ℕ) (x : countableSector N) :
    Tendsto (fun n => ∫ a in s n, countableLossCreationTwo M (u a) (v a)
      (countablePairAnnihilate N (countableWedge (M (u a)) (M (v a))) x) ∂μ) atTop
      (𝓝 (countableContinuousNoiseTwo μ p hp β hβ hb s hc hloc M hM hMc N x)) := by
  simpa only [hpw, countablePairFilter_wedge, countablePairLossOutput_wedge] using
    countableContinuousNoiseTwo_integral_tendsto μ p hp β hβ hb s hc hloc M hM hMc hm hu N x

end VortexGap.Fermion
