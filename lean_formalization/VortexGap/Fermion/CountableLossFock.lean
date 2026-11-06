import VortexGap.Fermion.CountableLossRotation
import VortexGap.Fermion.CountableFockFunctor
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped ComplexOrder
def countableLossFock (M : CountableOrbital →L[ℂ] CountableOrbital)
    (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1) : CountableSpace ≃ₗᵢ[ℂ] CountableSpace :=
  countableFockEquiv (countableLossRotation M hM hc)

theorem countableLossFock_sector (M : CountableOrbital →L[ℂ] CountableOrbital)
    (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1) (N : ℕ) (x : CountableSpace) :
    countableLossFock M hM hc x ∈ countableSector N ↔ x ∈ countableSector N :=
  countableFockEquiv_sector_iff _ N x

theorem countableLossFock_vacuum (M : CountableOrbital →L[ℂ] CountableOrbital)
    (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1) :
    countableLossFock M hM hc (countableKet ∅) = countableKet ∅ :=
  countableFockIsometry_vacuum _

theorem countableLossFock_create (M : CountableOrbital →L[ℂ] CountableOrbital)
    (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1) (v : CountableOrbital) (x : CountableSpace) :
    countableLossFock M hM hc
      (countableCreate (countableEnvOrbital v) ((countableLossFock M hM hc).symm x)) =
        countableCreate (countableLossEmbedding M hM hc v) x := by
  change countableFockEquiv _ (countableCreate _ ((countableFockEquiv _).symm x)) = _
  rw [countableFockEquiv_conjugate_create, countableLossRotation_env]

theorem countableLossFock_annihilate (M : CountableOrbital →L[ℂ] CountableOrbital)
    (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1) (v : CountableOrbital) (x : CountableSpace) :
    countableLossFock M hM hc
      (countableAnnihilate (countableEnvOrbital v) ((countableLossFock M hM hc).symm x)) =
        countableAnnihilate (countableLossEmbedding M hM hc v) x := by
  change countableFockEquiv _ (countableAnnihilate _ ((countableFockEquiv _).symm x)) = _
  rw [countableFockEquiv_conjugate_annihilate, countableLossRotation_env]

theorem countableLoss_create_tensor (M : CountableOrbital →L[ℂ] CountableOrbital)
    (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1) :
    ∀ v, countableSplitConjugate (countableCreate (countableLossEmbedding M hM hc v)) =
      countableEnvironmentAmplify (countableCreate (lossDefect M v)) +
        countableEnvironmentParity.comp (l2Amplify (Finset ℕ) (countableCreate (M v))) := by
  intro v
  have h : countableSplitConjugate (countableCreate (countableLossEmbedding M hM hc v)) =
      countableSplitConjugate (countableCreate (countableEnvOrbital (lossDefect M v))) +
      countableSplitConjugate (countableCreate (countableSysOrbital (M v))) := by
    ext x AB
    simp [countableLossEmbedding_apply, countableSplitConjugate_apply, map_add]
  rw [h, countableSplit_create_env_tensor, countableSplit_create_sys_tensor]

theorem countableLoss_annihilate_tensor (M : CountableOrbital →L[ℂ] CountableOrbital)
    (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1) :
    ∀ v, countableSplitConjugate (countableAnnihilate (countableLossEmbedding M hM hc v)) =
      countableEnvironmentAmplify (countableAnnihilate (lossDefect M v)) +
        countableEnvironmentParity.comp (l2Amplify (Finset ℕ) (countableAnnihilate (M v))) := by
  intro v
  have h : countableSplitConjugate (countableAnnihilate (countableLossEmbedding M hM hc v)) =
      countableSplitConjugate (countableAnnihilate (countableEnvOrbital (lossDefect M v))) +
      countableSplitConjugate (countableAnnihilate (countableSysOrbital (M v))) := by
    ext x AB
    simp [countableLossEmbedding_apply, countableAnnihilate_add, countableSplitConjugate_apply]
  rw [h, countableSplit_annihilate_env_tensor, countableSplit_annihilate_sys_tensor]
end VortexGap.Fermion
