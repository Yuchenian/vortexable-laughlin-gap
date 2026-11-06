import VortexGap.Frame.CountableContinuousOneSynthesis
import VortexGap.Frame.CountableContinuousTwoNoise

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory Filter VortexGap.Frame
open scoped InnerProduct ENNReal Topology ComplexOrder
variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ]
  (p : α → CountablePairSpace)
  (hp : ∀ q, MemLp (fun a => inner ℂ (p a) q) 2 μ)
  (β : ℝ) (hβ : 0 ≤ β)
  (hb : ∀ q, (∫ a, ‖inner ℂ (p a) q‖^2 ∂μ) ≤ β * ‖q‖^2)
  (s : ℕ → Set α) (hcov : AECover μ atTop s)
  (hloc : ∀ n, MemLp p 2 (μ.restrict (s n)))
  (M : CountableOrbital →L[ℂ] CountableOrbital) (hM : 0 ≤ M) (hMc : ‖M‖ ≤ 1)
  (U : α → CountableTwoFrame)
  (hU0 : AEStronglyMeasurable (fun a => U a (PiLp.single 2 0 1)) μ)
  (hU1 : AEStronglyMeasurable (fun a => U a (PiLp.single 2 1 1)) μ)
  (ω : α → ℝ) (hω : ∀ a, 0 < ω a) (hωm : AEStronglyMeasurable ω μ)
  (C : ℝ) (hC : 0 ≤ C)
  (hrowInt : ∀ᵐ a ∂μ, Integrable
    (fun b => traceNormTwo (countableTwoFrameOverlap (U a) (U b)) * ω b) μ)
  (hrow : ∀ᵐ a ∂μ,
    (∫ b, traceNormTwo (countableTwoFrameOverlap (U a) (U b)) * ω b ∂μ) ≤ C * ω a)

/-- Concrete one-environment creation synthesis after actual filtered annihilation. -/
def countableContinuousNoiseOne (N : ℕ) : countableSector N →L[ℂ] CountableSpace :=
  (countableContinuousOneLossSynthesis μ M hMc U hU0 hU1 ω hω hωm C hC hrowInt hrow).comp
    (countableContinuousFilteredAnalysis μ p hp β hβ hb s hcov hloc M hM hMc N)

theorem countableContinuousNoiseOne_relative
    (hm : Monotone s) (hu : ⋃ n, s n = Set.univ) (N : ℕ) (x : countableSector N) :
    ‖countableContinuousNoiseOne μ p hp β hβ hb s hcov hloc M hM hMc
      U hU0 hU1 ω hω hωm C hC hrowInt hrow N x‖^2 ≤
      C * ‖1-M^2‖ * (inner ℂ x (countablePairLift N ((countablePairFilter M hM).comp
        ((countableContinuousPairOperator μ p hp β hβ hb).comp (countablePairFilter M hM).adjoint))
        x)).re := by
  have h := countableContinuousOneLossSynthesis_norm_sq μ M hMc U hU0 hU1 ω hω hωm C hC hrowInt hrow hM
    (countableContinuousFilteredAnalysis μ p hp β hβ hb s hcov hloc M hM hMc N x)
  rw [countableContinuousFilteredAnalysis_norm_sq μ p hp β hβ hb s hcov hloc M hM hMc hm hu N x] at h
  exact h

theorem countableContinuousNoiseOne_cutoff (N : ℕ) (x : countableSector N) (n : ℕ) :
    countableContinuousOneLossSynthesis μ M hMc U hU0 hU1 ω hω hωm C hC hrowInt hrow
      (Frame.l2Cutoff μ (spanningSets μ n) (measurableSet_spanningSets μ n)
        (countableContinuousFilteredAnalysis μ p hp β hβ hb s hcov hloc M hM hMc N x)) =
      ∫ a in spanningSets μ n,
        countableLossCreationOne M (U a (PiLp.single 2 0 1)) (U a (PiLp.single 2 1 1))
          (countablePairAnnihilate N (countablePairFilter M hM (p a)) x) ∂μ := by
  rw [countableContinuousOneLossSynthesis_cutoff]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae
    (countableContinuousFilteredAnalysis_ae μ p hp β hβ hb s hcov hloc M hM hMc N x)] with a ha
  rw [ha]

include hp hβ hb hcov hloc hMc hU0 hU1 in
theorem countableContinuousNoiseOne_local_integrable (N : ℕ) (x : countableSector N) (n : ℕ) :
    Integrable (fun a => countableLossCreationOne M (U a (PiLp.single 2 0 1))
      (U a (PiLp.single 2 1 1)) (countablePairAnnihilate N (countablePairFilter M hM (p a)) x))
      (μ.restrict (spanningSets μ n)) := by
  have h := countableLossCreationOne_local_integrable μ M U hU0 hU1 n
    (countableContinuousFilteredAnalysis μ p hp β hβ hb s hcov hloc M hM hMc N x)
  apply h.congr
  filter_upwards [ae_restrict_of_ae
    (countableContinuousFilteredAnalysis_ae μ p hp β hβ hb s hcov hloc M hM hMc N x)] with a ha
  rw [ha]

theorem countableContinuousNoiseOne_integral_tendsto (N : ℕ) (x : countableSector N) :
    Tendsto (fun n => ∫ a in spanningSets μ n,
      countableLossCreationOne M (U a (PiLp.single 2 0 1)) (U a (PiLp.single 2 1 1))
        (countablePairAnnihilate N (countablePairFilter M hM (p a)) x) ∂μ) atTop
      (𝓝 (countableContinuousNoiseOne μ p hp β hβ hb s hcov hloc M hM hMc
        U hU0 hU1 ω hω hωm C hC hrowInt hrow N x)) := by
  have h := ((countableContinuousOneLossSynthesis μ M hMc U hU0 hU1 ω hω hωm C hC hrowInt hrow).continuous.tendsto
    (countableContinuousFilteredAnalysis μ p hp β hβ hb s hcov hloc M hM hMc N x)).comp
    (Frame.l2Cutoff_spanning_tendsto μ _)
  have he (n : ℕ) := countableContinuousNoiseOne_cutoff μ p hp β hβ hb s hcov hloc M hM hMc
    U hU0 hU1 ω hω hωm C hC hrowInt hrow N x n
  simpa only [Function.comp_def, he, countableContinuousNoiseOne,
    ContinuousLinearMap.comp_apply] using h

theorem countableContinuousNoiseOne_wedge_cutoff
    (hpw : ∀ a, p a = countableWedge (U a (PiLp.single 2 0 1)) (U a (PiLp.single 2 1 1)))
    (N : ℕ) (x : countableSector N) (n : ℕ) :
    countableContinuousOneLossSynthesis μ M hMc U hU0 hU1 ω hω hωm C hC hrowInt hrow
      (Frame.l2Cutoff μ (spanningSets μ n) (measurableSet_spanningSets μ n)
        (countableContinuousFilteredAnalysis μ p hp β hβ hb s hcov hloc M hM hMc N x)) =
      ∫ a in spanningSets μ n,
        countableLossCreationOne M (U a (PiLp.single 2 0 1)) (U a (PiLp.single 2 1 1))
          (countablePairAnnihilate N (countableWedge (M (U a (PiLp.single 2 0 1)))
            (M (U a (PiLp.single 2 1 1)))) x) ∂μ := by
  simpa only [hpw, countablePairFilter_wedge] using
    countableContinuousNoiseOne_cutoff μ p hp β hβ hb s hcov hloc M hM hMc
      U hU0 hU1 ω hω hωm C hC hrowInt hrow N x n

theorem countableContinuousNoiseOne_wedge_integral_tendsto
    (hpw : ∀ a, p a = countableWedge (U a (PiLp.single 2 0 1)) (U a (PiLp.single 2 1 1)))
    (N : ℕ) (x : countableSector N) :
    Tendsto (fun n => ∫ a in spanningSets μ n,
      countableLossCreationOne M (U a (PiLp.single 2 0 1)) (U a (PiLp.single 2 1 1))
        (countablePairAnnihilate N (countableWedge (M (U a (PiLp.single 2 0 1)))
          (M (U a (PiLp.single 2 1 1)))) x) ∂μ) atTop
      (𝓝 (countableContinuousNoiseOne μ p hp β hβ hb s hcov hloc M hM hMc
        U hU0 hU1 ω hω hωm C hC hrowInt hrow N x)) := by
  simpa only [hpw, countablePairFilter_wedge] using
    countableContinuousNoiseOne_integral_tendsto μ p hp β hβ hb s hcov hloc M hM hMc
      U hU0 hU1 ω hω hωm C hC hrowInt hrow N x

end VortexGap.Fermion
