import VortexGap.Frame.ContinuousAmplification
import VortexGap.Fermion.ExteriorNorm

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory
open scoped InnerProduct ENNReal ComplexOrder

variable {n : ℕ}
  (M : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))

/-- The existing CAR two-environment creation map, linear in its pair coefficient. -/
def twoLossCreationField : PairSpace n →L[ℂ] (Space n →L[ℂ] SplitSpace n n) :=
  (((LinearMap.toContinuousLinearMap :
    (Space n →ₗ[ℂ] SplitSpace n n) ≃ₗ[ℂ] (Space n →L[ℂ] SplitSpace n n)).toLinearMap).comp
    (fockProduct.comp (pairEmbed.comp (exteriorSquare (lossDefect M).toLinearMap)))).toContinuousLinearMap

theorem twoLossCreationField_apply (p : PairSpace n) (x : Space n) :
    twoLossCreationField M p x = twoLossCreation M p x := rfl

theorem pairStackProduct_environment (p : PairSpace n) (x : Space n) :
    pairEnvironmentEmbed (pairAmplify (exteriorSquare (lossDefect M).toLinearMap)
      (pairStackProduct p x)) = twoLossCreation M p x := by
  have hf (A : Finset (Fin n)) : pairFiber A (pairStackProduct p x) = x A • p := by
    ext i
    change p i * x A = x A * p i
    exact mul_comm _ _
  ext ⟨A,B⟩
  simp only [pairEnvironmentEmbed_apply, pairAmplify_fiber, hf, map_smul,
    PiLp.smul_apply, smul_eq_mul, twoLossCreation, fockProduct_apply]
  exact mul_comm _ _

variable {α : Type*} [MeasurableSpace α]
  (μ : Measure α) (p : α → PairSpace n) (hp : MemLp p 2 μ)

include hp in
theorem filteredPair_memLp : MemLp (fun a => exteriorSquare M.toLinearMap (p a)) 2 μ :=
  (LinearMap.toContinuousLinearMap (exteriorSquare M.toLinearMap)).comp_memLp' hp

/-- Actual integral of the concrete CAR output; no factorization is assumed. -/
def continuousTwoLossNoise : Space n →L[ℂ] SplitSpace n n :=
  ∫ a, (twoLossCreationField M (p a)).comp
    (LinearMap.toContinuousLinearMap (pairAnnihilate (exteriorSquare M.toLinearMap (p a)))) ∂μ

include hp in
theorem continuousTwoLossNoise_integrable :
    Integrable (fun a => (twoLossCreationField M (p a)).comp
      (LinearMap.toContinuousLinearMap (pairAnnihilate (exteriorSquare M.toLinearMap (p a))))) μ := by
  have hR := (twoLossCreationField M).comp_memLp' hp
  have hT := pairAnnihilate_memLp μ _ (filteredPair_memLp M μ p hp)
  apply (hR.norm.integrable_mul hT.norm).mono'
    ((ContinuousLinearMap.compL ℂ (Space n) (Space n) (SplitSpace n n)).aestronglyMeasurable_comp₂
      hR.aestronglyMeasurable hT.aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun a => ContinuousLinearMap.opNorm_comp_le _ _

include hp in
theorem continuousTwoLossNoise_apply (x : Space n) :
    continuousTwoLossNoise M μ p x = ∫ a,
      twoLossCreation M (p a) (pairAnnihilate (exteriorSquare M.toLinearMap (p a)) x) ∂μ := by
  exact ContinuousLinearMap.integral_apply (continuousTwoLossNoise_integrable M μ p hp) x

/-- The integral CAR expression equals the genuine synthesis/exterior-square factorization. -/
theorem continuousTwoLossNoise_factorization (x : Space n) :
    continuousTwoLossNoise M μ p x =
      pairEnvironmentEmbed (pairAmplify (exteriorSquare (lossDefect M).toLinearMap)
        (continuousPairSynthesisStack μ p hp
          (continuousFrameAnalysis μ (fun a => exteriorSquare M.toLinearMap (p a))
            (filteredPair_memLp M μ p hp) x))) := by
  haveI : CompleteSpace (PairStackSpace n) := PiLp.completeSpace 2 (fun _ => ℂ)
  let f := continuousFrameAnalysis μ (fun a => exteriorSquare M.toLinearMap (p a))
    (filteredPair_memLp M μ p hp) x
  let L := LinearMap.toContinuousLinearMap
    (pairEnvironmentEmbed.comp (pairAmplify (exteriorSquare (lossDefect M).toLinearMap)))
  change continuousTwoLossNoise M μ p x = L (continuousPairSynthesisStack μ p hp f)
  rw [continuousTwoLossNoise_apply M μ p hp, continuousPairSynthesisStack_integral,
    ← L.integral_comp_comm (pairStackProduct_integrable μ p hp f)]
  apply integral_congr_ae
  filter_upwards [continuousFrameAnalysis_ae μ _ (filteredPair_memLp M μ p hp) x] with a ha
  change twoLossCreation M (p a) (pairAnnihilate (exteriorSquare M.toLinearMap (p a)) x) =
    pairEnvironmentEmbed (pairAmplify (exteriorSquare (lossDefect M).toLinearMap)
      (pairStackProduct (p a) (f a)))
  rw [pairStackProduct_environment]
  change f a = _ at ha
  rw [ha]

include hp in
theorem continuousTwoLossNoise_finite [Fintype α] [MeasurableSingletonClass α] :
    continuousTwoLossNoise M μ p =
      LinearMap.toContinuousLinearMap (twoLossNoise M (fun a => μ.real {a}) p) := by
  haveI : CompleteSpace (SplitSpace n n) := PiLp.completeSpace 2 (fun _ => ℂ)
  haveI : CompleteSpace (Space n →L[ℂ] SplitSpace n n) := ContinuousLinearMap.instCompleteSpace
  rw [continuousTwoLossNoise, integral_fintype (continuousTwoLossNoise_integrable M μ p hp)]
  ext x AB
  simp [twoLossNoise, LinearMap.sum_apply, LinearMap.smul_apply,
    RCLike.real_smul_eq_coe_smul, twoLossCreationField_apply]

end VortexGap.Fermion

