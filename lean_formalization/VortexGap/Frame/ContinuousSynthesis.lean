import VortexGap.Frame.ContinuousAnalysis

noncomputable section
set_option autoImplicit false
namespace VortexGap.Frame
open MeasureTheory
open scoped InnerProduct ENNReal

variable {α E F : Type*} [MeasurableSpace α]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  (μ : Measure α) (T : α → E →L[ℂ] F) (hT : MemLp T 2 μ)

include hT in
theorem operatorSynthesis_integrable (f : Lp F 2 μ) :
    Integrable (fun a => (T a).adjoint (f a)) μ := by
  have hm := (ContinuousLinearMap.adjoint : (E →L[ℂ] F) ≃ₗᵢ⋆[ℂ] (F →L[ℂ] E)).continuous.comp_aestronglyMeasurable hT.aestronglyMeasurable
  apply (hT.norm.integrable_mul (Lp.memLp f).norm).mono'
    ((ContinuousLinearMap.id ℂ (F →L[ℂ] E)).aestronglyMeasurable_comp₂ hm (Lp.aestronglyMeasurable f))
  exact Filter.Eventually.of_forall fun a => by
    simpa only [ContinuousLinearMap.id_apply, ContinuousLinearMap.compL_apply, Pi.mul_apply, ContinuousLinearMap.adjoint.norm_map] using (T a).adjoint.le_opNorm (f a)

/-- The adjoint is the actual Bochner synthesis integral, not a postulated map. -/
theorem operatorAnalysis_adjoint_apply (f : Lp F 2 μ) :
    (operatorAnalysis μ T hT).adjoint f = ∫ a, (T a).adjoint (f a) ∂μ := by
  apply ext_inner_left ℂ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_right, ← integral_inner (operatorSynthesis_integrable μ T hT f), L2.inner_def]
  apply integral_congr_ae
  filter_upwards [operatorAnalysis_ae μ T hT x] with a ha
  rw [ha, ContinuousLinearMap.adjoint_inner_right]

include hT in
theorem operatorGram_integrable :
    Integrable (fun a => (T a).adjoint.comp (T a)) μ := by
  have hm := (ContinuousLinearMap.adjoint : (E →L[ℂ] F) ≃ₗᵢ⋆[ℂ] (F →L[ℂ] E)).continuous.comp_aestronglyMeasurable hT.aestronglyMeasurable
  apply (hT.norm.integrable_mul hT.norm).mono'
    ((ContinuousLinearMap.compL ℂ E F E).aestronglyMeasurable_comp₂ hm hT.aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun a => by
    simpa only [ContinuousLinearMap.id_apply, ContinuousLinearMap.compL_apply, Pi.mul_apply, ContinuousLinearMap.adjoint.norm_map] using (T a).adjoint.opNorm_comp_le (T a)

/-- The operator-valued integral agrees with the Gram operator of actual L2 analysis. -/
theorem operatorAnalysis_gram :
    (operatorAnalysis μ T hT).adjoint.comp (operatorAnalysis μ T hT) =
      ∫ a, (T a).adjoint.comp (T a) ∂μ := by
  apply ContinuousLinearMap.ext
  intro x
  rw [ContinuousLinearMap.comp_apply, operatorAnalysis_adjoint_apply,
    ContinuousLinearMap.integral_apply (operatorGram_integrable μ T hT)]
  apply integral_congr_ae
  filter_upwards [operatorAnalysis_ae μ T hT x] with a ha
  simp only [ha, ContinuousLinearMap.comp_apply]

/-- Changing a representative of the L2 input does not change synthesis. -/
theorem operatorSynthesis_representative (f : Lp F 2 μ) (g : α → F)
    (hg : f =ᵐ[μ] g) :
    (operatorAnalysis μ T hT).adjoint f = ∫ a, (T a).adjoint (g a) ∂μ := by
  rw [operatorAnalysis_adjoint_apply]
  apply integral_congr_ae
  filter_upwards [hg] with a ha
  rw [ha]

end VortexGap.Frame
