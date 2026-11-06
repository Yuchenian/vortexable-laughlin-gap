import VortexGap.Frame.CountableSlaterSchur
import VortexGap.Fermion.CountableContinuousLossOutput
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped InnerProduct ComplexOrder ComplexConjugate
variable {I : Type*} [Fintype I] (M : CountableOrbital →L[ℂ] CountableOrbital) (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1)
private theorem ann_sum (N : ℕ) (p : I → CountablePairSpace) :
    countablePairAnnihilate N (∑ i, p i) = ∑ i, countablePairAnnihilate N (p i) :=
  map_sum (countablePairAnnihilateWave N) _ _

private theorem tensor_sum (c : I → ℂ) (p : I → CountablePairSpace) (y : CountableSpace) :
    countablePairTensor (∑ i, c i • p i) y = ∑ i, c i • countablePairTensor (p i) y := by
  apply lp.ext
  funext a
  simp only [lp.coeFn_sum,countablePairTensor_apply,lp.coeFn_smul,Finset.sum_apply,Pi.smul_apply,
    smul_eq_mul,Finset.sum_smul,smul_smul]

theorem countableSlater_annihilate_system {N : ℕ} (c : I → ℂ) (U : I → CountableTwoFrame)
    (x : countableSector N) :
    let p := countableSlaterPair c U
    countablePairAnnihilate N (countablePairMap (countableLossEmbedding M hM hc) p)
      (countableFockSector countableSysOrbital N x) =
    countableFockIsometry countableSysOrbital (countablePairAnnihilate N (countablePairFilter M hM p) x) := by
  simp only [countableSlaterPair,map_sum,map_smul,countableWedge_map,countablePairFilter_wedge,
    ann_sum,countablePairAnnihilate_smul,sum_apply,smul_apply,countableLoss_pair_annihilate_system]

private theorem wedge_create_system {N : ℕ} (u v : CountableOrbital) (y : countableSector N) :
    ((countablePairAnnihilate (N+2) (countableWedge (countableLossEmbedding M hM hc u)
      (countableLossEmbedding M hM hc v))).adjoint (countableFockIsometry countableSysOrbital y) : CountableSpace) =
    countableFockIsometry countableSysOrbital ((countablePairAnnihilate (N+2) (countableWedge (M u) (M v))).adjoint (y : CountableSpace)) +
    countableLossCreationOne M u v y + countablePairLossOutput M (countablePairTensor (countableWedge u v) y) := by
  change ((countablePairAnnihilate _ _).adjoint (countableFockSector countableSysOrbital N y : countableSector N) : CountableSpace) = _
  rw [countablePairAnnihilate_wedge_adjoint,countablePairAnnihilate_wedge_adjoint,countablePairLossOutput_wedge]
  exact countableLoss_creation_output M hM hc u v y

theorem countableSlater_create_system {N : ℕ} (c : I → ℂ) (U : I → CountableTwoFrame)
    (y : countableSector N) :
    let p := countableSlaterPair c U
    ((countablePairAnnihilate (N+2) (countablePairMap (countableLossEmbedding M hM hc) p)).adjoint
      (countableFockIsometry countableSysOrbital y) : CountableSpace) =
    countableFockIsometry countableSysOrbital ((countablePairAnnihilate (N+2) (countablePairFilter M hM p)).adjoint (y : CountableSpace)) +
    (∑ i, c i • countableLossCreationOne M (U i (PiLp.single 2 0 1)) (U i (PiLp.single 2 1 1))) y +
    countablePairLossOutput M (countablePairTensor p y) := by
  dsimp only
  simp only [countableSlaterPair,map_sum,map_smul,countableWedge_map,countablePairFilter_wedge,ann_sum,
    countablePairAnnihilate_smul,map_smulₛₗ,starRingEnd_self_apply,sum_apply,smul_apply,
    Submodule.coe_sum,Submodule.coe_smul_of_tower,tensor_sum,map_sum,map_smul,wedge_create_system,
    smul_add,Finset.sum_add_distrib]

theorem countableSlater_rankOne_output {N : ℕ} (c : I → ℂ) (U : I → CountableTwoFrame) (x : countableSector (N+2)) :
    let p := countableSlaterPair c U
    let F := countablePairFilter M hM
    let P := countablePairMap (countableLossEmbedding M hM hc)
    let y := countablePairAnnihilate (N+2) (F p) x
    (countablePairLift (N+2) (InnerProductSpace.rankOne ℂ (P p) (P p))
      (countableFockSector countableSysOrbital (N+2) x) : CountableSpace) =
    countableFockIsometry countableSysOrbital
      (countablePairLift (N+2) (InnerProductSpace.rankOne ℂ (F p) (F p)) x) +
    (∑ i, c i • countableLossCreationOne M (U i (PiLp.single 2 0 1)) (U i (PiLp.single 2 1 1))) y +
    countablePairLossOutput M (countablePairTensor p y) := by
  dsimp only
  rw [countablePairLift_rankOne,countablePairLift_rankOne,ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply,
    countableSlater_annihilate_system]
  exact countableSlater_create_system M hM hc c U
    ⟨_, countablePairAnnihilate_sector _ x⟩

end VortexGap.Fermion
