import VortexGap.Frame.CountableContinuousOneSchur
import VortexGap.Frame.BesselSynthesis
import VortexGap.Fermion.CountableOneEnvironment

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory Filter VortexGap.Frame
open scoped InnerProduct ENNReal Topology ComplexOrder
variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ]
  (M : CountableOrbital →L[ℂ] CountableOrbital) (hc : ‖M‖ ≤ 1)
  (U : α → CountableTwoFrame)
  (hU0 : AEStronglyMeasurable (fun a => U a (PiLp.single 2 0 1)) μ)
  (hU1 : AEStronglyMeasurable (fun a => U a (PiLp.single 2 1 1)) μ)
  (ω : α → ℝ) (hω : ∀ a, 0 < ω a) (hωm : AEStronglyMeasurable ω μ)
  (C : ℝ) (hC : 0 ≤ C)
  (hrowInt : ∀ᵐ a ∂μ, Integrable
    (fun b => traceNormTwo (countableTwoFrameOverlap (U a) (U b)) * ω b) μ)
  (hrow : ∀ᵐ a ∂μ,
    (∫ b, traceNormTwo (countableTwoFrameOverlap (U a) (U b)) * ω b ∂μ) ≤ C * ω a)

include hU0 hU1 in
theorem countableOneFrameAdjoint_spanning_memLp (n : ℕ) :
    MemLp (fun a => (countableOneFrameCreation M (U a (PiLp.single 2 0 1))
      (U a (PiLp.single 2 1 1))).adjoint) 2 (μ.restrict (spanningSets μ n)) := by
  haveI : IsFiniteMeasure (μ.restrict (spanningSets μ n)) :=
    isFiniteMeasure_restrict.mpr (measure_spanningSets_lt_top μ n).ne
  exact countableOneFrameAdjoint_memLp _ M _ _ hU0.restrict hU1.restrict
    (fun a => by simp) (fun a => by simp)

include hU0 hU1 in
theorem countableOneFrame_local_integrable (n : ℕ) (f : Lp CountableSpace 2 μ) :
    Integrable (fun a => countableOneFrameCreation M (U a (PiLp.single 2 0 1))
      (U a (PiLp.single 2 1 1)) (f a)) (μ.restrict (spanningSets μ n)) := by
  have h := besselSynthesis_local_integrable μ
    (fun a => (countableOneFrameCreation M (U a (PiLp.single 2 0 1))
      (U a (PiLp.single 2 1 1))).adjoint) (spanningSets μ n)
    (countableOneFrameAdjoint_spanning_memLp μ M U hU0 hU1 n) f
  simpa only [ContinuousLinearMap.adjoint_adjoint] using h

theorem countableContinuousOneSynthesis_cutoff (n : ℕ) (f : Lp CountableSpace 2 μ) :
    countableContinuousOneSynthesis μ M hc U hU0 hU1 ω hω hωm C hC hrowInt hrow
      (l2Cutoff μ (spanningSets μ n) (measurableSet_spanningSets μ n) f) =
      ∫ a in spanningSets μ n, countableOneFrameCreation M (U a (PiLp.single 2 0 1))
        (U a (PiLp.single 2 1 1)) (f a) ∂μ := by
  unfold countableContinuousOneSynthesis countableContinuousOneAnalysis
  rw [besselSynthesis_cutoff_integral μ _ _ _ _ _ (spanningSets μ n)
    (measurableSet_spanningSets μ n) (countableOneFrameAdjoint_spanning_memLp μ M U hU0 hU1 n) f]
  simp only [ContinuousLinearMap.adjoint_adjoint]
  apply integral_congr_ae
  exact Eventually.of_forall fun _ => rfl

/-- The concrete one-environment loss action after the raw-Schur synthesis. -/
def countableContinuousOneLossSynthesis : Lp CountableSpace 2 μ →L[ℂ] CountableSpace :=
  (countableOneEnvironmentAction (lossDefect M)).comp
    (countableContinuousOneSynthesis μ M hc U hU0 hU1 ω hω hωm C hC hrowInt hrow)

theorem countableContinuousOneLossSynthesis_norm_sq (hM : 0 ≤ M) (f : Lp CountableSpace 2 μ) :
    ‖countableContinuousOneLossSynthesis μ M hc U hU0 hU1 ω hω hωm C hC hrowInt hrow f‖^2 ≤
      C * ‖1-M^2‖ * ‖f‖^2 := by
  let R := countableContinuousOneSynthesis μ M hc U hU0 hU1 ω hω hωm C hC hrowInt hrow
  have h := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg (R f)))).mpr
    (countableOneEnvironmentAction_norm_le (lossDefect M) (R f))
  rw [mul_pow, lossDefect_norm_sq M hM hc] at h
  calc
    _ ≤ ‖1-M^2‖ * ‖R f‖^2 := h
    _ ≤ ‖1-M^2‖ * (C * ‖f‖^2) := mul_le_mul_of_nonneg_left
      (countableContinuousOneSynthesis_norm_sq μ M hc U hU0 hU1 ω hω hωm C hC hrowInt hrow f)
      (norm_nonneg _)
    _ = _ := by ring

include hU0 hU1 in
theorem countableLossCreationOne_local_integrable (n : ℕ) (f : Lp CountableSpace 2 μ) :
    Integrable (fun a => countableLossCreationOne M (U a (PiLp.single 2 0 1))
      (U a (PiLp.single 2 1 1)) (f a)) (μ.restrict (spanningSets μ n)) := by
  have h := (countableOneEnvironmentAction (lossDefect M)).integrable_comp
    (countableOneFrame_local_integrable μ M U hU0 hU1 n f)
  simpa only [countableLossCreationOne_factorization] using h

theorem countableContinuousOneLossSynthesis_cutoff (n : ℕ) (f : Lp CountableSpace 2 μ) :
    countableContinuousOneLossSynthesis μ M hc U hU0 hU1 ω hω hωm C hC hrowInt hrow
      (l2Cutoff μ (spanningSets μ n) (measurableSet_spanningSets μ n) f) =
      ∫ a in spanningSets μ n, countableLossCreationOne M (U a (PiLp.single 2 0 1))
        (U a (PiLp.single 2 1 1)) (f a) ∂μ := by
  change countableOneEnvironmentAction (lossDefect M)
    (countableContinuousOneSynthesis μ M hc U hU0 hU1 ω hω hωm C hC hrowInt hrow
      (l2Cutoff μ (spanningSets μ n) (measurableSet_spanningSets μ n) f)) = _
  rw [countableContinuousOneSynthesis_cutoff,
    ← (countableOneEnvironmentAction (lossDefect M)).integral_comp_comm
      (countableOneFrame_local_integrable μ M U hU0 hU1 n f)]
  apply integral_congr_ae
  exact Eventually.of_forall fun a => (countableLossCreationOne_factorization M _ _ (f a)).symm

theorem countableContinuousOneLossSynthesis_integral_tendsto (f : Lp CountableSpace 2 μ) :
    Tendsto (fun n => ∫ a in spanningSets μ n,
      countableLossCreationOne M (U a (PiLp.single 2 0 1)) (U a (PiLp.single 2 1 1)) (f a) ∂μ)
      atTop (𝓝 (countableContinuousOneLossSynthesis μ M hc U hU0 hU1 ω hω hωm C hC hrowInt hrow f)) := by
  have h := ((countableContinuousOneLossSynthesis μ M hc U hU0 hU1 ω hω hωm C hC hrowInt hrow).continuous.tendsto f).comp
    (l2Cutoff_spanning_tendsto μ f)
  have he (n : ℕ) := countableContinuousOneLossSynthesis_cutoff μ M hc U hU0 hU1 ω hω hωm C hC hrowInt hrow n f
  simpa only [Function.comp_def, he] using h

end VortexGap.Fermion
