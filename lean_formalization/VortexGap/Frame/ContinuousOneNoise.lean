import VortexGap.Frame.ContinuousOneSynthesis
import VortexGap.Frame.ContinuousTwoNoise

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory
open scoped InnerProduct ENNReal

variable {n : ℕ}
  (M : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))

theorem oneLossCreation_continuous_factorization (u v : EuclideanSpace ℂ (Fin n)) :
    LinearMap.toContinuousLinearMap (oneLossCreation M u v) =
      (LinearMap.toContinuousLinearMap
        (orbitalEnvironmentEmbed.comp (orbitalAmplify (lossDefect M)))).comp
          (LinearMap.toContinuousLinearMap (oneFrameCreation M u v)) := by
  apply ContinuousLinearMap.ext
  intro x
  exact oneLossCreation_factorization M u v x

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
  (u v : α → EuclideanSpace ℂ (Fin n))
  (hu : AEStronglyMeasurable u μ) (hv : AEStronglyMeasurable v μ)
  (hun : ∀ a, ‖u a‖ ≤ 1) (hvn : ∀ a, ‖v a‖ ≤ 1)

include hu hv hun hvn in
theorem oneLossCreation_memLp :
    MemLp (fun a => LinearMap.toContinuousLinearMap (oneLossCreation M (u a) (v a))) 2 μ := by
  have hR := oneFrameCreation_memLp M μ u v hu hv hun hvn
  have h := ((ContinuousLinearMap.compL ℂ (Space n) (OrbitalStackSpace n) (SplitSpace n n))
    (LinearMap.toContinuousLinearMap (orbitalEnvironmentEmbed.comp (orbitalAmplify (lossDefect M))))).comp_memLp' hR
  apply h.ae_eq
  exact Filter.Eventually.of_forall fun a => by
    change (LinearMap.toContinuousLinearMap
      (orbitalEnvironmentEmbed.comp (orbitalAmplify (lossDefect M)))).comp
        (LinearMap.toContinuousLinearMap (oneFrameCreation M (u a) (v a))) = _
    exact (oneLossCreation_continuous_factorization M (u a) (v a)).symm

/-- The original mixed CAR creation followed by filtered pair annihilation, integrated literally. -/
def continuousOneLossNoise : Space n →L[ℂ] SplitSpace n n :=
  ∫ a, (LinearMap.toContinuousLinearMap (oneLossCreation M (u a) (v a))).comp
    (LinearMap.toContinuousLinearMap
      (pairAnnihilate (exteriorSquare M.toLinearMap (wedgePair (u a) (v a))))) ∂μ

include hu hv hun hvn in
theorem continuousOneLossNoise_integrable :
    Integrable (fun a => (LinearMap.toContinuousLinearMap (oneLossCreation M (u a) (v a))).comp
      (LinearMap.toContinuousLinearMap
        (pairAnnihilate (exteriorSquare M.toLinearMap (wedgePair (u a) (v a)))))) μ := by
  have hR := oneLossCreation_memLp M μ u v hu hv hun hvn
  have hp := wedgePair_memLp μ u v hu hv hun hvn
  have hB := pairAnnihilate_memLp μ _ (filteredPair_memLp M μ _ hp)
  apply (hR.norm.integrable_mul hB.norm).mono'
    ((ContinuousLinearMap.compL ℂ (Space n) (Space n) (SplitSpace n n)).aestronglyMeasurable_comp₂
      hR.aestronglyMeasurable hB.aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun a => ContinuousLinearMap.opNorm_comp_le _ _

include hu hv hun hvn in
theorem continuousOneLossNoise_apply (x : Space n) :
    continuousOneLossNoise M μ u v x = ∫ a,
      oneLossCreation M (u a) (v a)
        (pairAnnihilate (exteriorSquare M.toLinearMap (wedgePair (u a) (v a))) x) ∂μ :=
  ContinuousLinearMap.integral_apply (continuousOneLossNoise_integrable M μ u v hu hv hun hvn) x

theorem continuousOneLossNoise_factorization (x : Space n) :
    continuousOneLossNoise M μ u v x =
      orbitalEnvironmentEmbed (orbitalAmplify (lossDefect M)
        (continuousOneFrameSynthesis M μ u v hu hv hun hvn
          (continuousFrameAnalysis μ (fun a => exteriorSquare M.toLinearMap (wedgePair (u a) (v a)))
            (filteredPair_memLp M μ _ (wedgePair_memLp μ u v hu hv hun hvn)) x))) := by
  haveI : CompleteSpace (OrbitalStackSpace n) := PiLp.completeSpace 2 (fun _ => ℂ)
  let hp := filteredPair_memLp M μ _ (wedgePair_memLp μ u v hu hv hun hvn)
  let f := continuousFrameAnalysis μ (fun a => exteriorSquare M.toLinearMap (wedgePair (u a) (v a))) hp x
  let L := LinearMap.toContinuousLinearMap (orbitalEnvironmentEmbed.comp (orbitalAmplify (lossDefect M)))
  change continuousOneLossNoise M μ u v x = L (continuousOneFrameSynthesis M μ u v hu hv hun hvn f)
  rw [continuousOneLossNoise_apply M μ u v hu hv hun hvn, continuousOneFrameSynthesis_apply,
    ← L.integral_comp_comm (oneFrameCreation_apply_integrable M μ u v hu hv hun hvn f)]
  apply integral_congr_ae
  filter_upwards [continuousFrameAnalysis_ae μ _ hp x] with a ha
  change f a = _ at ha
  change oneLossCreation M (u a) (v a)
      (pairAnnihilate (exteriorSquare M.toLinearMap (wedgePair (u a) (v a))) x) =
    orbitalEnvironmentEmbed (orbitalAmplify (lossDefect M) (oneFrameCreation M (u a) (v a) (f a)))
  rw [ha, oneLossCreation_factorization]

include hu hv hun hvn in
theorem continuousOneLossNoise_finite [Fintype α] [MeasurableSingletonClass α] :
    continuousOneLossNoise M μ u v =
      LinearMap.toContinuousLinearMap (oneLossNoise M (fun a => μ.real {a}) u v) := by
  haveI : CompleteSpace (SplitSpace n n) := PiLp.completeSpace 2 (fun _ => ℂ)
  haveI : CompleteSpace (Space n →L[ℂ] SplitSpace n n) := ContinuousLinearMap.instCompleteSpace
  rw [continuousOneLossNoise, integral_fintype (continuousOneLossNoise_integrable M μ u v hu hv hun hvn)]
  ext x AB
  simp [oneLossNoise, LinearMap.sum_apply, LinearMap.smul_apply, RCLike.real_smul_eq_coe_smul]

end VortexGap.Fermion

