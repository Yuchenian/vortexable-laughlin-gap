import VortexGap.Frame.CountableContinuousPair

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory
open scoped InnerProduct ENNReal

local instance pairOperatorNormed :
    NormedAddCommGroup (CountablePairSpace →L[ℂ] CountablePairSpace) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance sectorOperatorNormed (N : ℕ) :
    NormedAddCommGroup (countableSector N →L[ℂ] countableSector N) :=
  ContinuousLinearMap.toNormedAddCommGroup

/-- The concrete CAR lift is bounded as a map between operator spaces. -/
def countablePairLiftContinuous (N : ℕ) :
    (CountablePairSpace →L[ℂ] CountablePairSpace) →L[ℂ]
      (countableSector N →L[ℂ] countableSector N) := by
  exact (countablePairLiftLinear N).mkContinuous (N.choose 2 : ℝ)
    (fun Q => countablePairLift_opNorm_le N Q)

variable {α : Type*} [MeasurableSpace α]
  (μ : Measure α) (p : α → CountablePairSpace)

include μ in
theorem countablePairRankOne_integrable (hp : MemLp p 2 μ) :
    Integrable (fun a => InnerProductSpace.rankOne ℂ (p a) (p a)) μ := by
  have hc : Continuous (fun q : CountablePairSpace => InnerProductSpace.rankOne ℂ q q) := by
    simp_rw [InnerProductSpace.rankOne_def']
    exact (ContinuousLinearMap.toSpanSingletonLIE ℂ CountablePairSpace).continuous.clm_comp
      (innerSL ℂ).continuous
  apply (hp.norm.integrable_mul hp.norm).mono'
    (hc.comp_aestronglyMeasurable hp.aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun a => by
    simp only [InnerProductSpace.norm_rankOne, Pi.mul_apply, le_refl]

/-- On a locally norm-integrable pair field, the integral Hamiltonian is the CAR lift. -/
theorem countablePairLift_integral (hp : MemLp p 2 μ) (N : ℕ) :
    countablePairLift N (∫ a, InnerProductSpace.rankOne ℂ (p a) (p a) ∂μ) =
      ∫ a, (countablePairAnnihilate N (p a)).adjoint.comp
        (countablePairAnnihilate N (p a)) ∂μ := by
  change countablePairLiftContinuous N (∫ a, InnerProductSpace.rankOne ℂ (p a) (p a) ∂μ) = _
  rw [← ContinuousLinearMap.integral_comp_comm (𝕜 := ℂ)
    (E := CountablePairSpace →L[ℂ] CountablePairSpace)
    (Fₗ := countableSector N →L[ℂ] countableSector N)
    (countablePairLiftContinuous N) (countablePairRankOne_integrable μ p hp)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun a => countablePairLift_rankOne N (p a) (p a)

theorem countablePairHamiltonian_integrable (hp : MemLp p 2 μ) (N : ℕ) :
    Integrable (fun a => (countablePairAnnihilate N (p a)).adjoint.comp
      (countablePairAnnihilate N (p a))) μ := by
  have h := ContinuousLinearMap.integrable_comp
    (H := CountablePairSpace →L[ℂ] CountablePairSpace)
    (E := countableSector N →L[ℂ] countableSector N)
    (σ := RingHom.id ℂ) (countablePairLiftContinuous N)
    (countablePairRankOne_integrable μ p hp)
  convert h using 1
  funext a
  exact (countablePairLift_rankOne N (p a) (p a)).symm

/-- The cutoff of the weak frame operator gives the original restricted CAR interaction. -/
theorem countableContinuousPairCutoff_lift_integral
    (hp : ∀ q, MemLp (fun a => inner ℂ (p a) q) 2 μ)
    (β : ℝ) (hβ : 0 ≤ β)
    (hb : ∀ q, (∫ a, ‖inner ℂ (p a) q‖^2 ∂μ) ≤ β * ‖q‖^2)
    (s : Set α) (hs : MeasurableSet s) (hloc : MemLp p 2 (μ.restrict s)) (N : ℕ) :
    countablePairLift N (countableContinuousPairCutoff μ p hp β hβ hb s hs) =
      ∫ a in s, (countablePairAnnihilate N (p a)).adjoint.comp
        (countablePairAnnihilate N (p a)) ∂μ := by
  rw [countableContinuousPairCutoff_integral μ p hp β hβ hb s hs hloc]
  exact countablePairLift_integral (μ.restrict s) p hloc N

end VortexGap.Fermion

