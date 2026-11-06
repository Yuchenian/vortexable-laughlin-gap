import VortexGap.Fermion.CountableVacuumTensor
import VortexGap.Fermion.CountableReferenceGap
import VortexGap.Fermion.CountableFockPullback
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped ComplexOrder

theorem countableLoss_annihilate_system
    (M : CountableOrbital →L[ℂ] CountableOrbital) (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1)
    (v : CountableOrbital) (x : CountableSpace) :
    countableAnnihilate (countableLossEmbedding M hM hc v)
      (countableFockIsometry countableSysOrbital x) =
    countableFockIsometry countableSysOrbital (countableAnnihilate (M v) x) := by
  rw [countableFock_annihilate_pullback, countableSysOrbital_adjoint_loss]

theorem countableLoss_double_annihilate_system
    (M : CountableOrbital →L[ℂ] CountableOrbital) (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1)
    (u v : CountableOrbital) (x : CountableSpace) :
    countableAnnihilate (countableLossEmbedding M hM hc v)
      (countableAnnihilate (countableLossEmbedding M hM hc u)
        (countableFockIsometry countableSysOrbital x)) =
    countableFockIsometry countableSysOrbital
      (countableAnnihilate (M v) (countableAnnihilate (M u) x)) := by
  rw [countableLoss_annihilate_system, countableLoss_annihilate_system]

theorem countableLoss_pair_annihilate_system
    (M : CountableOrbital →L[ℂ] CountableOrbital) (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1)
    {N : ℕ} (u v : CountableOrbital) (x : countableSector N) :
    countablePairAnnihilate N
      (countableWedge (countableLossEmbedding M hM hc u) (countableLossEmbedding M hM hc v))
      (countableFockSector countableSysOrbital N x) =
    countableFockIsometry countableSysOrbital
      (countablePairAnnihilate N (countableWedge (M u) (M v)) x) := by
  rw [countablePairAnnihilate_wedge, countablePairAnnihilate_wedge]
  exact countableLoss_double_annihilate_system M hM hc u v x

theorem countableLoss_pair_annihilate_vacuum
    (M : CountableOrbital →L[ℂ] CountableOrbital) (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1)
    {N : ℕ} (u v : CountableOrbital) (x : countableSector N) :
    countableFockSplit (countablePairAnnihilate N
      (countableWedge (countableLossEmbedding M hM hc u) (countableLossEmbedding M hM hc v))
      (countableFockSector countableSysOrbital N x)) =
    countableVacuumTensor (countablePairAnnihilate N (countableWedge (M u) (M v)) x) := by
  rw [countableLoss_pair_annihilate_system, countableFockSplit_system]
end VortexGap.Fermion
