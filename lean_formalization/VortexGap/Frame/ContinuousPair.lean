import VortexGap.Frame.ContinuousSynthesis
import VortexGap.Fermion.Pair

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory
open scoped InnerProduct ENNReal

/-- The original CAR pair creation map, bundled continuously in its pair coefficient. -/
def pairCreationField (n : ℕ) : PairSpace n →L[ℂ] (Space n →L[ℂ] Space n) :=
  ({ toFun := fun p => (LinearMap.toContinuousLinearMap (pairCreate p))
     map_add' := by intro p q; simp only [pairCreate_add, map_add]
     map_smul' := by intro z p; simp only [pairCreate_smul, map_smul, RingHom.id_apply] } :
    PairSpace n →ₗ[ℂ] (Space n →L[ℂ] Space n)).toContinuousLinearMap

theorem pairCreationField_apply {n : ℕ} (p : PairSpace n) :
    pairCreationField n p = (LinearMap.toContinuousLinearMap (pairCreate p)) := rfl

theorem pairAnnihilate_continuous {n : ℕ} :
    Continuous (fun p : PairSpace n => (LinearMap.toContinuousLinearMap (pairAnnihilate p))) := by
  have heq : (fun p : PairSpace n => (LinearMap.toContinuousLinearMap (pairAnnihilate p))) =
      fun p => (pairCreationField n p).adjoint := by
    funext p
    rw [pairCreationField_apply, ← LinearMap.adjoint_toContinuousLinearMap,
      ← pairAnnihilate_adjoint, LinearMap.adjoint_adjoint]
  rw [heq]
  exact ContinuousLinearMap.adjoint.continuous.comp (pairCreationField n).continuous

theorem pairAnnihilate_opNorm_le {n : ℕ} (p : PairSpace n) :
    ‖(LinearMap.toContinuousLinearMap (pairAnnihilate p))‖ ≤ ‖pairCreationField n‖ * ‖p‖ := by
  have hn : ‖(LinearMap.toContinuousLinearMap (pairAnnihilate p))‖ = ‖pairCreationField n p‖ := by
    rw [pairCreationField_apply, ← pairAnnihilate_adjoint,
      LinearMap.adjoint_toContinuousLinearMap, ContinuousLinearMap.adjoint.norm_map]
  rw [hn]
  exact (pairCreationField n).le_opNorm p

variable {α : Type*} [MeasurableSpace α] {n : ℕ}
  (μ : Measure α) (p : α → PairSpace n) (hp : MemLp p 2 μ)

include hp in
theorem pairAnnihilate_memLp :
    MemLp (fun a => (LinearMap.toContinuousLinearMap (pairAnnihilate (p a)))) 2 μ := by
  apply hp.of_le_mul (pairAnnihilate_continuous.comp_aestronglyMeasurable hp.aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun a => pairAnnihilate_opNorm_le (p a)

/-- Analysis uses the actual CAR B(p), on the full finite-mode Fock space. -/
def continuousFrameAnalysis : Space n →L[ℂ] Lp (Space n) 2 μ :=
  Frame.operatorAnalysis μ (fun a => (LinearMap.toContinuousLinearMap (pairAnnihilate (p a))))
    (pairAnnihilate_memLp μ p hp)

/-- The actual Bochner integral of B(p)* B(p). Defined independently of its analysis identity. -/
def continuousFrameHamiltonian : Space n →L[ℂ] Space n :=
  ∫ a, ((LinearMap.toContinuousLinearMap (pairAnnihilate (p a)))).adjoint.comp
    (LinearMap.toContinuousLinearMap (pairAnnihilate (p a))) ∂μ

include hp in
theorem continuousFrame_integrable :
    Integrable (fun a => ((LinearMap.toContinuousLinearMap (pairAnnihilate (p a)))).adjoint.comp
      (LinearMap.toContinuousLinearMap (pairAnnihilate (p a)))) μ :=
  Frame.operatorGram_integrable μ _ (pairAnnihilate_memLp μ p hp)

theorem continuousFrameAnalysis_ae (x : Space n) :
    continuousFrameAnalysis μ p hp x =ᵐ[μ] fun a => pairAnnihilate (p a) x :=
  Frame.operatorAnalysis_ae μ _ _ x

theorem continuousFrameAnalysis_gram :
    (continuousFrameAnalysis μ p hp).adjoint.comp (continuousFrameAnalysis μ p hp) =
      continuousFrameHamiltonian μ p :=
  Frame.operatorAnalysis_gram μ _ _

theorem continuousFrameAnalysis_energy (x : Space n) :
    ‖continuousFrameAnalysis μ p hp x‖^2 =
      (inner ℂ x (continuousFrameHamiltonian μ p x)).re := by
  rw [← continuousFrameAnalysis_gram μ p hp, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right, ← RCLike.re_eq_complex_re,
    ← norm_sq_eq_re_inner (𝕜 := ℂ)]

include hp in
theorem continuousFrameHamiltonian_energy (x : Space n) :
    (inner ℂ x (continuousFrameHamiltonian μ p x)).re =
      ∫ a, ‖pairAnnihilate (p a) x‖^2 ∂μ := by
  rw [← continuousFrameAnalysis_energy μ p hp]
  exact Frame.operatorAnalysis_norm_sq μ _ _ x

theorem continuousFrameAnalysis_synthesis (f : Lp (Space n) 2 μ) :
    (continuousFrameAnalysis μ p hp).adjoint f = ∫ a, pairCreate (p a) (f a) ∂μ := by
  rw [continuousFrameAnalysis, Frame.operatorAnalysis_adjoint_apply]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun a => by
    change (pairAnnihilate (p a)).adjoint (f a) = pairCreate (p a) (f a)
    rw [pairAnnihilate_adjoint]

end VortexGap.Fermion
