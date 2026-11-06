import VortexGap.Frame.CountableContinuousLift
import VortexGap.Frame.BesselSynthesis

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory
open scoped InnerProduct ENNReal

attribute [local instance] pairOperatorNormed
local instance pairStackOperatorNormed :
    NormedAddCommGroup (CountablePairStackSpace →L[ℂ] CountablePairStackSpace) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance pairContractOperatorNormed :
    NormedAddCommGroup (CountablePairStackSpace →L[ℂ] CountableSpace) :=
  ContinuousLinearMap.toNormedAddCommGroup

/-- Amplification is a bounded linear map on the actual pair-operator space. -/
def countablePairAmplifyContinuous :
    (CountablePairSpace →L[ℂ] CountablePairSpace) →L[ℂ]
      (CountablePairStackSpace →L[ℂ] CountablePairStackSpace) := by
  let L : (CountablePairSpace →L[ℂ] CountablePairSpace) →ₗ[ℂ]
      (CountablePairStackSpace →L[ℂ] CountablePairStackSpace) :=
    { toFun := countablePairAmplify
      map_add' := countablePairAmplify_add
      map_smul' := countablePairAmplify_smul }
  exact L.mkContinuous 1 (fun Q => by
    change ‖countablePairAmplify Q‖ ≤ 1 * ‖Q‖
    simpa only [one_mul] using countablePairAmplify_opNorm_le Q)

/-- Dependence of the concrete pair contraction on its pair wavefunction. -/
def countablePairContractWave :
    CountablePairSpace →L⋆[ℂ] (CountablePairStackSpace →L[ℂ] CountableSpace) := by
  let L : CountablePairSpace →ₗ⋆[ℂ] (CountablePairStackSpace →L[ℂ] CountableSpace) :=
    { toFun := countablePairContract
      map_add' := countablePairContract_add
      map_smul' := countablePairContract_smul }
  exact ⟨L, AddMonoidHomClass.continuous_of_bound L 1
    (fun p => by
      change ‖countablePairContract p‖ ≤ 1 * ‖p‖
      simpa only [one_mul] using countablePairContract_opNorm_le p)⟩

theorem countablePairContract_adjoint (p : CountablePairSpace) (x : CountableSpace) :
    (countablePairContract p).adjoint x = countablePairTensor p x := by
  apply ext_inner_left ℂ
  intro z
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact (countablePairTensor_inner_contract_right p x z).symm

theorem countablePairAmplify_rankOne_gram (p : CountablePairSpace) :
    countablePairAmplify (InnerProductSpace.rankOne ℂ p p) =
      (countablePairContract p).adjoint.comp (countablePairContract p) := by
  apply ContinuousLinearMap.ext
  intro z
  rw [countablePairAmplify_rankOne, ContinuousLinearMap.comp_apply, countablePairContract_adjoint]

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) (p : α → CountablePairSpace)

theorem countablePairContractField_memLp (hp : MemLp p 2 μ) :
    MemLp (fun a => countablePairContract (p a)) 2 μ := by
  apply hp.of_le_mul (E := CountablePairStackSpace →L[ℂ] CountableSpace)
    (f := fun a => countablePairContract (p a)) (c := 1)
    (countablePairContractWave.continuous.comp_aestronglyMeasurable hp.aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun a => by
    simpa only [one_mul] using countablePairContract_opNorm_le (p a)

/-- The spectator-amplified local pair integral is the Gram of the actual contraction field. -/
theorem countablePairAmplify_integral (hp : MemLp p 2 μ) :
    countablePairAmplify (∫ a, InnerProductSpace.rankOne ℂ (p a) (p a) ∂μ) =
      ∫ a, (countablePairContract (p a)).adjoint.comp (countablePairContract (p a)) ∂μ := by
  change countablePairAmplifyContinuous (∫ a, InnerProductSpace.rankOne ℂ (p a) (p a) ∂μ) = _
  rw [← ContinuousLinearMap.integral_comp_comm (𝕜 := ℂ)
    (E := CountablePairSpace →L[ℂ] CountablePairSpace)
    (Fₗ := CountablePairStackSpace →L[ℂ] CountablePairStackSpace)
    countablePairAmplifyContinuous (countablePairRankOne_integrable μ p hp)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun a => countablePairAmplify_rankOne_gram (p a)

theorem countablePairContract_local_energy (hp : MemLp p 2 μ) (z : CountablePairStackSpace) :
    (inner ℂ z (countablePairAmplify
      (∫ a, InnerProductSpace.rankOne ℂ (p a) (p a) ∂μ) z)).re =
      ∫ a, ‖countablePairContract (p a) z‖^2 ∂μ := by
  have hg := Frame.operatorAnalysis_gram (E := CountablePairStackSpace) (F := CountableSpace)
    μ (fun a => countablePairContract (p a)) (countablePairContractField_memLp μ p hp)
  have he := congrArg (fun T : CountablePairStackSpace →L[ℂ] CountablePairStackSpace =>
    (inner ℂ z (T z)).re) hg
  rw [countablePairAmplify_integral μ p hp]
  refine he.symm.trans ?_
  change (inner ℂ z ((Frame.operatorAnalysis μ _ (countablePairContractField_memLp μ p hp)).adjoint
    (Frame.operatorAnalysis μ _ (countablePairContractField_memLp μ p hp) z))).re = _
  rw [ContinuousLinearMap.adjoint_inner_right, ← RCLike.re_eq_complex_re,
    ← norm_sq_eq_re_inner (𝕜 := ℂ)]
  exact Frame.operatorAnalysis_norm_sq μ _ (countablePairContractField_memLp μ p hp) z

end VortexGap.Fermion

