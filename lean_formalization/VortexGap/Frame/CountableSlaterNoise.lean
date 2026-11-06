import VortexGap.Frame.CountableSlaterSchur
import VortexGap.Frame.CountableContinuousOneNoise
import VortexGap.Frame.CountablePairFrameFields
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory Filter VortexGap.Frame
open scoped InnerProduct ENNReal Topology ComplexOrder
variable {α I : Type*} [Fintype I] [MeasurableSpace α] (μ : Measure α)
  (M : CountableOrbital →L[ℂ] CountableOrbital) (c : α → I → ℂ) (U : α → I → CountableTwoFrame)

theorem countableSlaterPair_memLp (hl : ∀ i, MemLp (fun a => c a i) 2 μ)
    (hu : ∀ i (l : Fin 2), AEStronglyMeasurable (fun a => U a i (PiLp.single 2 l 1)) μ) :
    MemLp (fun a => countableSlaterPair (c a) (U a)) 2 μ := by
  refine memLp_finsetSum (f := fun (i : I) (a : α) => c a i • countableWedge
    (U a i (PiLp.single 2 0 1)) (U a i (PiLp.single 2 1 1))) Finset.univ ?_
  intro i _
  have hm := countableWedge_continuous.comp_aestronglyMeasurable ((hu i 0).prodMk (hu i 1))
  apply (hl i).of_le_mul (c := 1) ((hl i).aestronglyMeasurable.smul hm)
  apply Eventually.of_forall
  intro a
  change ‖c a i • countableWedge _ _‖ ≤ _
  rw [norm_smul,one_mul]
  have hh := countableWedge_norm_le (U a i (PiLp.single 2 0 1)) (U a i (PiLp.single 2 1 1))
  simpa using mul_le_mul_of_nonneg_left hh (norm_nonneg (c a i))

def countableSlaterLossColumn (M : CountableOrbital →L[ℂ] CountableOrbital) (c : I → ℂ) (U : I → CountableTwoFrame) :=
  ∑ i, c i • countableLossCreationOne M (U i (PiLp.single 2 0 1)) (U i (PiLp.single 2 1 1))

theorem countableSlaterLossColumn_factor (z : CountableSpace) (c : I → ℂ) (U : I → CountableTwoFrame) :
    countableSlaterLossColumn M c U z =
      countableOneEnvironmentAction (lossDefect M) (countableSlaterColumn M c U z) := by
  simp [countableSlaterLossColumn,countableSlaterColumn,countableLossCreationOne_factorization]

variable [SigmaFinite μ] (hc : ‖M‖ ≤ 1)
    (hl : ∀ n i, MemLp (fun a => c a i) 2 (μ.restrict (spanningSets μ n)))
    (hu : ∀ i (l : Fin 2), AEStronglyMeasurable (fun a => U a i (PiLp.single 2 l 1)) μ)
    (ω : α → ℝ) (hω : ∀ a, 0 < ω a) (hωm : AEStronglyMeasurable ω μ)
    (C : ℝ) (hC : 0 ≤ C)
    (hrowInt : ∀ᵐ a ∂μ, Integrable (fun b => countableSlaterKernel (c a) (c b) (U a) (U b) * ω b) μ)
    (hrow : ∀ᵐ a ∂μ, (∫ b, countableSlaterKernel (c a) (c b) (U a) (U b) * ω b ∂μ) ≤ C * ω a)


private abbrev analysis := countableSlaterAnalysis μ M c U hc hl hu ω hω hωm C hC hrowInt hrow

def countableSlaterLossSynthesis : Lp CountableSpace 2 μ →L[ℂ] CountableSpace :=
  (countableOneEnvironmentAction (lossDefect M)).comp (analysis μ M c U hc hl hu ω hω hωm C hC hrowInt hrow).adjoint

theorem countableSlaterLossSynthesis_norm_sq (hM : 0 ≤ M) (f : Lp CountableSpace 2 μ) :
    ‖countableSlaterLossSynthesis μ M c U hc hl hu ω hω hωm C hC hrowInt hrow f‖^2 ≤
      C*‖1-M^2‖*‖f‖^2 := by
  let z := (analysis μ M c U hc hl hu ω hω hωm C hC hrowInt hrow).adjoint f
  have ha := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg z))).mpr
    (countableOneEnvironmentAction_norm_le (lossDefect M) z)
  rw [mul_pow,lossDefect_norm_sq M hM hc] at ha
  exact ha.trans ((mul_le_mul_of_nonneg_left
    (countableSlater_synthesis_bound μ M c U hc hl hu ω hω hωm C hC hrowInt hrow f)
    (norm_nonneg _)).trans_eq (by ring))

include hl hu in
theorem countableSlaterLossColumn_local_integrable (n : ℕ) (f : Lp CountableSpace 2 μ) :
    Integrable (fun a => countableSlaterLossColumn M (c a) (U a) (f a)) (μ.restrict (spanningSets μ n)) := by
  have hi := besselSynthesis_local_integrable μ _ (spanningSets μ n)
    (countableSlaterAdjoint_memLp _ M c U (hl n) (fun i l => (hu i l).restrict)) f
  simp only [ContinuousLinearMap.adjoint_adjoint] at hi
  simpa only [countableSlaterLossColumn_factor] using (countableOneEnvironmentAction (lossDefect M)).integrable_comp hi

theorem countableSlaterLossSynthesis_cutoff (n : ℕ) (f : Lp CountableSpace 2 μ) :
    countableSlaterLossSynthesis μ M c U hc hl hu ω hω hωm C hC hrowInt hrow
      (l2Cutoff μ (spanningSets μ n) (measurableSet_spanningSets μ n) f) =
      ∫ a in spanningSets μ n, countableSlaterLossColumn M (c a) (U a) (f a) ∂μ := by
  have ht := countableSlaterAdjoint_memLp _ M c U (hl n) (fun i l => (hu i l).restrict)
  have hi := besselSynthesis_local_integrable μ _ (spanningSets μ n) ht f
  simp only [ContinuousLinearMap.adjoint_adjoint] at hi
  simp only [countableSlaterLossSynthesis,ContinuousLinearMap.comp_apply,analysis,countableSlaterAnalysis]
  rw [besselSynthesis_cutoff_integral μ _ _ _ _ _ (spanningSets μ n) (measurableSet_spanningSets μ n) ht f]
  simp only [ContinuousLinearMap.adjoint_adjoint]
  refine ((countableOneEnvironmentAction (lossDefect M)).integral_comp_comm hi).symm.trans ?_
  exact integral_congr_ae (Eventually.of_forall fun a => (countableSlaterLossColumn_factor M _ _ _).symm)

theorem countableSlaterLossSynthesis_limit (f : Lp CountableSpace 2 μ) :
    Tendsto (fun n => ∫ a in spanningSets μ n, countableSlaterLossColumn M (c a) (U a) (f a) ∂μ)
      atTop (𝓝 (countableSlaterLossSynthesis μ M c U hc hl hu ω hω hωm C hC hrowInt hrow f)) := by
  have h := ((countableSlaterLossSynthesis μ M c U hc hl hu ω hω hωm C hC hrowInt hrow).continuous.tendsto f).comp
    (l2Cutoff_spanning_tendsto μ f)
  simpa only [Function.comp_def,countableSlaterLossSynthesis_cutoff] using h

end VortexGap.Fermion
