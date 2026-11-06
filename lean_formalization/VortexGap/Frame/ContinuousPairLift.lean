import VortexGap.Frame.ContinuousPair
import VortexGap.Fermion.LossReference
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory OAI.LaughlinGap.Occupation
open scoped InnerProduct ENNReal BigOperators

/-- The original finite-mode pair lift, with the operator norms on both spaces. -/
def pairLiftContinuous (n : ℕ) :
    (PairSpace n →L[ℂ] PairSpace n) →L[ℂ] (Space n →L[ℂ] Space n) :=
  ({ toFun := fun Q => LinearMap.toContinuousLinearMap (pairLift Q.toLinearMap)
     map_add' := by
       intro Q R
       simp only [ContinuousLinearMap.toLinearMap_add, pairLift_add, map_add]
     map_smul' := by
       intro z Q
       simp only [ContinuousLinearMap.toLinearMap_smul, pairLift_smul, map_smul, RingHom.id_apply] } :
    (PairSpace n →L[ℂ] PairSpace n) →ₗ[ℂ] (Space n →L[ℂ] Space n)).toContinuousLinearMap

theorem pairLiftContinuous_rankOne {n : ℕ} (p : PairSpace n) :
    pairLiftContinuous n (InnerProductSpace.rankOne ℂ p p) =
      (LinearMap.toContinuousLinearMap (pairAnnihilate p)).adjoint.comp
        (LinearMap.toContinuousLinearMap (pairAnnihilate p)) := by
  apply ContinuousLinearMap.ext
  intro x
  change pairLift (pairRankOne p) x = ((pairAnnihilate p).adjoint * pairAnnihilate p) x
  rw [pairLift_rankOne]

variable {α : Type*} [MeasurableSpace α] {n : ℕ}
  (μ : Measure α) (p : α → PairSpace n) (hp : MemLp p 2 μ)

/-- The actual two-particle frame operator. -/
def continuousPairOperator : PairSpace n →L[ℂ] PairSpace n :=
  ∫ a, InnerProductSpace.rankOne ℂ (p a) (p a) ∂μ

include hp in
theorem continuousPairOperator_integrable :
    Integrable (fun a => InnerProductSpace.rankOne ℂ (p a) (p a)) μ := by
  have hc : Continuous (fun q : PairSpace n => InnerProductSpace.rankOne ℂ q q) := by
    simp_rw [InnerProductSpace.rankOne_def']
    exact (ContinuousLinearMap.toSpanSingletonLIE ℂ (PairSpace n)).continuous.clm_comp
      (innerSL ℂ).continuous
  apply (hp.norm.integrable_mul hp.norm).mono'
    (hc.comp_aestronglyMeasurable hp.aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun a => by
    simp only [InnerProductSpace.norm_rankOne, Pi.mul_apply, le_refl]

include hp in
/-- Integration commutes with the concrete CAR lift. -/
theorem continuousFrameHamiltonian_pairLift :
    continuousFrameHamiltonian μ p = pairLiftContinuous n (continuousPairOperator μ p) := by
  haveI : CompleteSpace (Space n) := PiLp.completeSpace 2 (fun _ => ℂ)
  haveI : CompleteSpace (PairSpace n) := PiLp.completeSpace 2 (fun _ => ℂ)
  haveI : CompleteSpace (Space n →L[ℂ] Space n) := ContinuousLinearMap.instCompleteSpace
  haveI : CompleteSpace (PairSpace n →L[ℂ] PairSpace n) := ContinuousLinearMap.instCompleteSpace
  change (∫ a, _ ∂μ) = pairLiftContinuous n (∫ a, _ ∂μ)
  rw [← (pairLiftContinuous n).integral_comp_comm (continuousPairOperator_integrable μ p hp)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun a => (pairLiftContinuous_rankOne (p a)).symm

include hp in
theorem continuousFrameHamiltonian_positive : (continuousFrameHamiltonian μ p).IsPositive := by
  rw [← continuousFrameAnalysis_gram μ p hp]
  exact ContinuousLinearMap.isPositive_adjoint_comp_self _

include hp in
theorem continuousFrameHamiltonian_vacuum :
    continuousFrameHamiltonian μ p (ket ∅) = 0 := by
  rw [continuousFrameHamiltonian_pairLift μ p hp]
  exact pairLift_vacuum _

include hp in
theorem continuousFrameHamiltonian_oneParticle (v : EuclideanSpace ℂ (Fin n)) :
    continuousFrameHamiltonian μ p (create v (ket ∅)) = 0 := by
  rw [continuousFrameHamiltonian_pairLift μ p hp]
  exact pairLift_oneParticle _ v

theorem continuousPairOperator_congr_ae (q : α → PairSpace n) (heq : p =ᵐ[μ] q) :
    continuousPairOperator μ p = continuousPairOperator μ q := by
  apply integral_congr_ae
  filter_upwards [heq] with a ha
  rw [ha]

theorem continuousFrameHamiltonian_congr_ae (q : α → PairSpace n) (heq : p =ᵐ[μ] q) :
    continuousFrameHamiltonian μ p = continuousFrameHamiltonian μ q := by
  apply integral_congr_ae
  filter_upwards [heq] with a ha
  rw [ha]

include hp in
/-- On a finite label measure this is exactly the previous weighted Hamiltonian. -/
theorem continuousFrameHamiltonian_finite [Fintype α] [MeasurableSingletonClass α] :
    continuousFrameHamiltonian μ p =
      LinearMap.toContinuousLinearMap (frameHamiltonian (fun a => μ.real {a}) p) := by
  haveI : CompleteSpace (PairSpace n) := PiLp.completeSpace 2 (fun _ => ℂ)
  haveI : CompleteSpace (PairSpace n →L[ℂ] PairSpace n) := ContinuousLinearMap.instCompleteSpace
  rw [continuousFrameHamiltonian_pairLift μ p hp, continuousPairOperator,
    integral_fintype (continuousPairOperator_integrable μ p hp)]
  have heq : (∑ a, μ.real {a} • InnerProductSpace.rankOne ℂ (p a) (p a)) =
      LinearMap.toContinuousLinearMap (∑ a, (μ.real {a} : ℂ) • pairRankOne (p a)) := by
    apply ContinuousLinearMap.ext
    intro q
    simp [LinearMap.sum_apply, LinearMap.smul_apply, pairRankOne,
      RCLike.real_smul_eq_coe_smul]
  rw [heq]
  rfl

end VortexGap.Fermion
