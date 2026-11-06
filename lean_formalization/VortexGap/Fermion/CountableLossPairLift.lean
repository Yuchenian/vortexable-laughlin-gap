import VortexGap.Fermion.CountablePairUnitaryCovariance
import VortexGap.Fermion.CountableLossFock
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped ComplexOrder

theorem countablePair_conjugation_algebra
    (A B Q : CountablePairSpace →L[ℂ] CountablePairSpace) :
    A.comp ((B.comp (Q.comp B.adjoint)).comp A.adjoint) =
      (A.comp B).comp (Q.comp (A.comp B).adjoint) := by
  simp only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc]

theorem countablePairConjugate_comp
    (J K : CountableOrbital →ₗᵢ[ℂ] CountableOrbital)
    (Q : CountablePairSpace →L[ℂ] CountablePairSpace) :
    countablePairConjugate J (countablePairConjugate K Q) =
      countablePairConjugate (J.comp K) Q := by
  have h : countablePairMap (J.comp K) = (countablePairMap J).comp (countablePairMap K) := by
    apply ContinuousLinearMap.ext
    intro p
    exact (countablePairMap_comp J K p).symm
  unfold countablePairConjugate
  rw [h]
  exact countablePair_conjugation_algebra _ _ _

theorem countableLoss_pair_conjugate
    (M : CountableOrbital →L[ℂ] CountableOrbital) (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1)
    (Q : CountablePairSpace →L[ℂ] CountablePairSpace) :
    countablePairConjugate (countableLossRotation M hM hc).toLinearIsometry
      (countablePairConjugate countableEnvOrbital Q) =
    countablePairConjugate (countableLossEmbedding M hM hc) Q := by
  rw [countablePairConjugate_comp]
  have h : (countableLossRotation M hM hc).toLinearIsometry.comp countableEnvOrbital =
      countableLossEmbedding M hM hc := by
    apply LinearIsometry.ext
    exact countableLossRotation_env M hM hc
  rw [h]

/-- The actual loss-mode Hamiltonian is the unitary rotation of the reference
Hamiltonian embedded in the environment modes, on the entire total-N space. -/
theorem countableLoss_pairLift_conjugation
    (M : CountableOrbital →L[ℂ] CountableOrbital) (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1)
    (N : ℕ) (Q : CountablePairSpace →L[ℂ] CountablePairSpace) :
    countablePairLift N (countablePairConjugate (countableLossEmbedding M hM hc) Q) =
      (countableFockSectorEquiv (countableLossRotation M hM hc) N :
        countableSector N →L[ℂ] countableSector N).comp
      ((countablePairLift N (countablePairConjugate countableEnvOrbital Q)).comp
        (countableFockSectorEquiv (countableLossRotation M hM hc) N :
          countableSector N →L[ℂ] countableSector N).adjoint) := by
  rw [← countableLoss_pair_conjugate M hM hc Q]
  exact countablePairLift_unitary_conjugation _ N _
end VortexGap.Fermion
