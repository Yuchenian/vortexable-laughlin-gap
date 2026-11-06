import VortexGap.Frame.CountablePairAmplifiedIntegral
import VortexGap.Frame.LocalBessel
import VortexGap.Frame.SchurAnalysis

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory Filter
open scoped InnerProduct ENNReal Topology
attribute [local instance] pairOperatorNormed pairStackOperatorNormed pairContractOperatorNormed
variable {α : Type*} [MeasurableSpace α] (μ : Measure α) (p : α → CountablePairSpace)
  (hp : ∀ q, MemLp (fun a => inner ℂ (p a) q) 2 μ)
  (β : ℝ) (hβ : 0 ≤ β)
  (hb : ∀ q, (∫ a, ‖inner ℂ (p a) q‖^2 ∂μ) ≤ β * ‖q‖^2)

include hp hβ hb in
theorem countablePairContract_local_bound (s : Set α) (hs : MeasurableSet s)
    (hloc : MemLp p 2 (μ.restrict s)) (z : CountablePairStackSpace) :
    (∫ a in s, ‖countablePairContract (p a) z‖^2 ∂μ) ≤ β * ‖z‖^2 := by
  rw [← countablePairContract_local_energy (μ.restrict s) p hloc z,
    ← countableContinuousPairCutoff_integral μ p hp β hβ hb s hs hloc]
  let H := countablePairAmplify (countableContinuousPairCutoff μ p hp β hβ hb s hs)
  have hn : ‖H‖ ≤ β := (countablePairAmplify_opNorm_le _).trans
    (countableContinuousPairCutoff_norm_le μ p hp β hβ hb s hs)
  calc
    _ ≤ ‖z‖ * ‖H z‖ := re_inner_le_norm (𝕜 := ℂ) z (H z)
    _ ≤ ‖z‖ * (β * ‖z‖) :=
      mul_le_mul_of_nonneg_left (H.le_of_opNorm_le hn z) (norm_nonneg z)
    _ = _ := by ring

variable (s : ℕ → Set α) (hc : AECover μ atTop s)
  (hloc : ∀ n, MemLp p 2 (μ.restrict (s n)))

include hp hβ hb hc hloc in
/-- The original pair Bessel bound survives the complete spectator fiber, with no N factor. -/
theorem countablePairContract_global_bessel (z : CountablePairStackSpace) :
    MemLp (fun a => countablePairContract (p a) z) 2 μ ∧
      (∫ a, ‖countablePairContract (p a) z‖^2 ∂μ) ≤ β * ‖z‖^2 := by
  have hf (n : ℕ) : MemLp (fun a => countablePairContract (p a) z) 2 (μ.restrict (s n)) :=
    Frame.operatorApply_memLp _ _ (countablePairContractField_memLp _ p (hloc n)) z
  have hbound (n : ℕ) :
      (∫ a in s n, ‖countablePairContract (p a) z‖^2 ∂μ) ≤ β * ‖z‖^2 :=
    countablePairContract_local_bound μ p hp β hβ hb (s n) (hc.measurableSet n) (hloc n) z
  exact ⟨Frame.localL2_memLp μ s hc _ hf _ hbound, Frame.localL2_integral_le μ s hc _ hf _ hbound⟩

/-- Actual contraction analysis on the complete pair-spectator Hilbert space. -/
def countableContinuousPairStackAnalysis : CountablePairStackSpace →L[ℂ] Lp CountableSpace 2 μ :=
  Frame.besselAnalysis μ (fun a => countablePairContract (p a))
    (fun z => (countablePairContract_global_bessel μ p hp β hβ hb s hc hloc z).1) β hβ
    (fun z => (countablePairContract_global_bessel μ p hp β hβ hb s hc hloc z).2)

/-- The bounded S tensor I, defined as the adjoint of actual contraction analysis. -/
def countableContinuousPairStackSynthesis : Lp CountableSpace 2 μ →L[ℂ] CountablePairStackSpace :=
  (countableContinuousPairStackAnalysis μ p hp β hβ hb s hc hloc).adjoint

theorem countableContinuousPairStackAnalysis_ae (z : CountablePairStackSpace) :
    countableContinuousPairStackAnalysis μ p hp β hβ hb s hc hloc z =ᵐ[μ]
      fun a => countablePairContract (p a) z :=
  Frame.besselAnalysis_ae μ _ _ _ _ _ z

theorem countableContinuousPairStackSynthesis_norm_sq (f : Lp CountableSpace 2 μ) :
    ‖countableContinuousPairStackSynthesis μ p hp β hβ hb s hc hloc f‖^2 ≤ β * ‖f‖^2 := by
  apply Frame.analysis_norm_sq_of_adjoint_bound _ β hβ
  intro z
  rw [countableContinuousPairStackSynthesis, ContinuousLinearMap.adjoint_adjoint,
    countableContinuousPairStackAnalysis, Frame.besselAnalysis_norm_sq]
  exact (countablePairContract_global_bessel μ p hp β hβ hb s hc hloc z).2

include hloc in
theorem countablePairTensor_local_integrable (n : ℕ) (f : Lp CountableSpace 2 μ) :
    Integrable (fun a => countablePairTensor (p a) (f a)) (μ.restrict (s n)) := by
  have h := Frame.besselSynthesis_local_integrable μ (fun a => countablePairContract (p a))
    (s n) (countablePairContractField_memLp _ p (hloc n)) f
  simpa only [countablePairContract_adjoint] using h

/-- The global synthesis is identified with the genuine local tensor integral on each cutoff. -/
theorem countableContinuousPairStackSynthesis_cutoff (n : ℕ) (f : Lp CountableSpace 2 μ) :
    countableContinuousPairStackSynthesis μ p hp β hβ hb s hc hloc
      (Frame.l2Cutoff μ (s n) (hc.measurableSet n) f) =
      ∫ a in s n, countablePairTensor (p a) (f a) ∂μ := by
  change (Frame.besselAnalysis μ (fun a => countablePairContract (p a)) _ _ _ _).adjoint _ = _
  rw [Frame.besselSynthesis_cutoff_integral μ _ _ _ _ _ (s n) (hc.measurableSet n)
    (countablePairContractField_memLp _ p (hloc n)) f]
  apply integral_congr_ae
  exact Eventually.of_forall fun a => countablePairContract_adjoint (p a) (f a)

theorem countableContinuousPairStackSynthesis_integral_tendsto
    (hm : Monotone s) (hu : ⋃ n, s n = Set.univ) (f : Lp CountableSpace 2 μ) :
    Tendsto (fun n => ∫ a in s n, countablePairTensor (p a) (f a) ∂μ) atTop
      (𝓝 (countableContinuousPairStackSynthesis μ p hp β hβ hb s hc hloc f)) := by
  have h := ((countableContinuousPairStackSynthesis μ p hp β hβ hb s hc hloc).continuous.tendsto f).comp
    (Frame.l2Cutoff_tendsto μ s hc.measurableSet hm hu f)
  have he (n : ℕ) := countableContinuousPairStackSynthesis_cutoff μ p hp β hβ hb s hc hloc n f
  simpa only [Function.comp_def, he] using h

end VortexGap.Fermion

