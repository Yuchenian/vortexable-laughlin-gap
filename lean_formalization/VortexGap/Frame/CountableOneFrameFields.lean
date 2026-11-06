import VortexGap.Fermion.CountableOneFrame
import VortexGap.Frame.SchurAnalysis

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory
open scoped InnerProduct ENNReal

theorem countableEnvironmentProduct_continuous :
    Continuous (fun u : CountableOrbital => countableEnvironmentProduct u) := by
  exact (countableCreate.continuous.comp countableEnvOrbital.continuous).clm_comp continuous_const

theorem countableEnvironmentProduct_opNorm_le (u : CountableOrbital) :
    ‖countableEnvironmentProduct u‖ ≤ ‖u‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg u)
  intro x
  change ‖countableCreate (countableEnvOrbital u) (countableFockIsometry countableSysOrbital x)‖ ≤ _
  simpa only [countableEnvOrbital.norm_map,
    (countableFockIsometry countableSysOrbital).norm_map] using
    countableCreate_norm_le (countableEnvOrbital u) (countableFockIsometry countableSysOrbital x)

theorem countableOneFrameCreation_continuous
    (M : CountableOrbital →L[ℂ] CountableOrbital) :
    Continuous (fun z : CountableOrbital × CountableOrbital =>
      countableOneFrameCreation M z.1 z.2) := by
  exact ((countableEnvironmentProduct_continuous.comp continuous_fst).clm_comp
    (countableCreate.continuous.comp (M.continuous.comp continuous_snd))).sub
    ((countableEnvironmentProduct_continuous.comp continuous_snd).clm_comp
      (countableCreate.continuous.comp (M.continuous.comp continuous_fst)))

theorem countableOneFrameCreation_opNorm_bound
    (M : CountableOrbital →L[ℂ] CountableOrbital) (u v : CountableOrbital)
    (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    ‖countableOneFrameCreation M u v‖ ≤ 2 * ‖M‖ := by
  have hmu : ‖countableCreate (M u)‖ ≤ ‖M‖ := by
    apply (countableCreate_opNorm_le _).trans
    exact (M.le_opNorm u).trans (by simpa using mul_le_mul_of_nonneg_left hu (norm_nonneg M))
  have hmv : ‖countableCreate (M v)‖ ≤ ‖M‖ := by
    apply (countableCreate_opNorm_le _).trans
    exact (M.le_opNorm v).trans (by simpa using mul_le_mul_of_nonneg_left hv (norm_nonneg M))
  have hpu := (countableEnvironmentProduct_opNorm_le u).trans hu
  have hpv := (countableEnvironmentProduct_opNorm_le v).trans hv
  calc
    _ ≤ ‖(countableEnvironmentProduct u).comp (countableCreate (M v))‖ +
        ‖(countableEnvironmentProduct v).comp (countableCreate (M u))‖ := norm_sub_le _ _
    _ ≤ ‖countableEnvironmentProduct u‖ * ‖countableCreate (M v)‖ +
        ‖countableEnvironmentProduct v‖ * ‖countableCreate (M u)‖ :=
      add_le_add (ContinuousLinearMap.opNorm_comp_le _ _) (ContinuousLinearMap.opNorm_comp_le _ _)
    _ ≤ 1 * ‖M‖ + 1 * ‖M‖ := by gcongr
    _ = _ := by ring

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
  (M : CountableOrbital →L[ℂ] CountableOrbital) (u v : α → CountableOrbital)
  (hu : AEStronglyMeasurable u μ) (hv : AEStronglyMeasurable v μ)
  (hun : ∀ a, ‖u a‖ ≤ 1) (hvn : ∀ a, ‖v a‖ ≤ 1)

include hu hv hun hvn in
/-- Actual CAR one-environment columns are locally norm-square-integrable.
This finite-measure lemma is used only on the exhausting label sets. -/
theorem countableOneFrameCreation_memLp :
    MemLp (fun a => countableOneFrameCreation M (u a) (v a)) 2 μ := by
  apply MemLp.of_bound
    ((countableOneFrameCreation_continuous M).comp_aestronglyMeasurable (hu.prodMk hv))
    (2 * ‖M‖)
  exact Filter.Eventually.of_forall fun a =>
    countableOneFrameCreation_opNorm_bound M (u a) (v a) (hun a) (hvn a)

include hu hv hun hvn in
theorem countableOneFrameAdjoint_memLp :
    MemLp (fun a => (countableOneFrameCreation M (u a) (v a)).adjoint) 2 μ := by
  have hR := countableOneFrameCreation_memLp μ M u v hu hv hun hvn
  apply hR.of_le_mul (c := 1)
    ((ContinuousLinearMap.adjoint : (CountableSpace →L[ℂ] CountableSpace) ≃ₗᵢ⋆[ℂ]
      (CountableSpace →L[ℂ] CountableSpace)).continuous.comp_aestronglyMeasurable hR.aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun a => by
    simp only [ContinuousLinearMap.adjoint.norm_map, one_mul, le_refl]

end VortexGap.Fermion

