import VortexGap.Frame.ContinuousAction
import VortexGap.Frame.ContinuousOneNoise
import VortexGap.Fermion.LossMoments

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory
open scoped InnerProduct ENNReal ComplexOrder

variable {α : Type*} [MeasurableSpace α] {n : ℕ}

/-- The original frame embedded through the actual CAR loss isometry J=(E,M). -/
def continuousLossHamiltonian
    (M : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1) (μ : Measure α) (p : α → PairSpace n) :
    Space (n+n) →L[ℂ] Space (n+n) :=
  continuousFrameHamiltonian μ
    (fun a => exteriorSquare (finiteLossEmbedding M hM hc).toLinearMap (p a))

/-- Sector support survives a Bochner integral, proved through actual occupation coordinates. -/
theorem environmentSector_integral {m K : ℕ} (μ : Measure α) (f : α → SplitSpace n m)
    (hf : Integrable f μ) (hsector : ∀ᵐ a ∂μ, f a ∈ environmentSector n m K) :
    (∫ a, f a ∂μ) ∈ environmentSector n m K := by
  haveI : CompleteSpace (SplitSpace n m) := PiLp.completeSpace 2 (fun _ => ℂ)
  intro A B hA
  let L := PiLp.proj (𝕜 := ℂ) 2 (fun _ : Finset (Fin n) × Finset (Fin m) => ℂ) (A,B)
  change L (∫ a, f a ∂μ) = 0
  rw [← L.integral_comp_comm hf]
  apply integral_eq_zero_of_ae
  filter_upwards [hsector] with a ha
  exact ha A B hA

variable (M : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
  (μ : Measure α)

theorem continuousTwoLossNoise_action_integrable (p : α → PairSpace n) (hp : MemLp p 2 μ)
    (x : Space n) :
    Integrable (fun a => twoLossCreation M (p a)
      (pairAnnihilate (exteriorSquare M.toLinearMap (p a)) x)) μ :=
  (ContinuousLinearMap.apply ℂ (SplitSpace n n) x).integrable_comp
    (continuousTwoLossNoise_integrable M μ p hp)

theorem continuousTwoLossNoise_sector (p : α → PairSpace n) (hp : MemLp p 2 μ) (x : Space n) :
    continuousTwoLossNoise M μ p x ∈ environmentSector n n 2 := by
  rw [continuousTwoLossNoise_apply M μ p hp]
  exact environmentSector_integral μ _ (continuousTwoLossNoise_action_integrable M μ p hp x)
    (Filter.Eventually.of_forall fun a => twoLossCreation_sector M (p a) _)

theorem continuousLossHamiltonian_adjoint (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1)
    (p : α → PairSpace n) (hp : MemLp p 2 μ) :
    (continuousLossHamiltonian M hM hc μ p).adjoint = continuousLossHamiltonian M hM hc μ p :=
  continuousFrameHamiltonian_adjoint μ _
    (exteriorPair_memLp μ p hp (finiteLossEmbedding M hM hc).toLinearMap)

variable [IsFiniteMeasure μ] (u v : α → EuclideanSpace ℂ (Fin n))
  (hu : AEStronglyMeasurable u μ) (hv : AEStronglyMeasurable v μ)
  (hun : ∀ a, ‖u a‖ ≤ 1) (hvn : ∀ a, ‖v a‖ ≤ 1)

include hu hv hun hvn in
theorem continuousOneLossNoise_action_integrable (x : Space n) :
    Integrable (fun a => oneLossCreation M (u a) (v a)
      (pairAnnihilate (exteriorSquare M.toLinearMap (wedgePair (u a) (v a))) x)) μ :=
  (ContinuousLinearMap.apply ℂ (SplitSpace n n) x).integrable_comp
    (continuousOneLossNoise_integrable M μ u v hu hv hun hvn)

include hu hv hun hvn in
theorem continuousOneLossNoise_sector (x : Space n) :
    continuousOneLossNoise M μ u v x ∈ environmentSector n n 1 := by
  rw [continuousOneLossNoise_apply M μ u v hu hv hun hvn]
  exact environmentSector_integral μ _ (continuousOneLossNoise_action_integrable M μ u v hu hv hun hvn x)
    (Filter.Eventually.of_forall fun a => oneLossCreation_sector M (u a) (v a) _)

include hu hv hun hvn in
/-- Exact three-sector output of the continuous CAR Hamiltonian, derived by integration. -/
theorem continuous_loss_vacuum (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1) (x : Space n) :
    fockSplit n n (continuousLossHamiltonian M hM hc μ (fun a => wedgePair (u a) (v a))
      (lossVacuum n x)) =
      environmentVacuum n n (continuousFrameHamiltonian μ
        (fun a => exteriorSquare M.toLinearMap (wedgePair (u a) (v a))) x) +
        continuousOneLossNoise M μ u v x +
        continuousTwoLossNoise M μ (fun a => wedgePair (u a) (v a)) x := by
  haveI : CompleteSpace (Space (n+n)) := PiLp.completeSpace 2 (fun _ => ℂ)
  haveI : CompleteSpace (Space n) := PiLp.completeSpace 2 (fun _ => ℂ)
  haveI : CompleteSpace (SplitSpace n n) := PiLp.completeSpace 2 (fun _ => ℂ)
  let p := fun a => wedgePair (u a) (v a)
  have hp : MemLp p 2 μ := wedgePair_memLp μ u v hu hv hun hvn
  have hJ := exteriorPair_memLp μ p hp (finiteLossEmbedding M hM hc).toLinearMap
  have hF := continuousFrameAction_integrable μ _ (filteredPair_memLp M μ p hp) x
  have h0 : Integrable (fun a => environmentVacuum n n
      (pairCreate (exteriorSquare M.toLinearMap (p a))
        (pairAnnihilate (exteriorSquare M.toLinearMap (p a)) x))) μ :=
    (LinearMap.toContinuousLinearMap (environmentVacuum n n)).integrable_comp hF
  have h1 := continuousOneLossNoise_action_integrable M μ u v hu hv hun hvn x
  have h2 := continuousTwoLossNoise_action_integrable M μ p hp x
  have h01 : Integrable (fun a => environmentVacuum n n
      (pairCreate (exteriorSquare M.toLinearMap (p a))
        (pairAnnihilate (exteriorSquare M.toLinearMap (p a)) x)) +
      oneLossCreation M (u a) (v a)
        (pairAnnihilate (exteriorSquare M.toLinearMap (p a)) x)) μ := h0.add h1
  have henv : (∫ a, environmentVacuum n n
      (pairCreate (exteriorSquare M.toLinearMap (p a))
        (pairAnnihilate (exteriorSquare M.toLinearMap (p a)) x)) ∂μ) =
      environmentVacuum n n (∫ a, pairCreate (exteriorSquare M.toLinearMap (p a))
        (pairAnnihilate (exteriorSquare M.toLinearMap (p a)) x) ∂μ) :=
    (LinearMap.toContinuousLinearMap (environmentVacuum n n)).integral_comp_comm hF
  have hsplit (f : α → Space (n+n)) :
      fockSplit n n (∫ a, f a ∂μ) = ∫ a, fockSplit n n (f a) ∂μ :=
    ((fockSplit n n).toLinearIsometry.integral_comp_comm f).symm
  rw [continuousLossHamiltonian, continuousFrameHamiltonian_apply μ _ hJ]
  rw [hsplit]
  dsimp only [p]
  simp_rw [lossVacuum_apply, loss_pairAnnihilate_vacuum, loss_pairCreate_vacuum]
  rw [integral_add h01 h2, integral_add h0 h1, henv]
  rw [← continuousFrameHamiltonian_apply μ _ (filteredPair_memLp M μ p hp),
    ← continuousOneLossNoise_apply M μ u v hu hv hun hvn,
    ← continuousTwoLossNoise_apply M μ p hp]

end VortexGap.Fermion

