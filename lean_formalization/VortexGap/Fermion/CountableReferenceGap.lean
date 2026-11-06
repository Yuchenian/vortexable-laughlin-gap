import VortexGap.Fermion.CountableEnvironmentStrongLift
import VortexGap.Operator.IsometricIntertwining
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped ComplexOrder

/-- The concrete environment-embedded pair Hamiltonian inherits its quadratic
gap from precisely the original reference sectors k<=N. -/
theorem countableEnvironmentLift_gap (N : ℕ)
    (Q : CountablePairSpace →L[ℂ] CountablePairSpace) (γ : ℝ)
    (h : ∀ k ≤ N, (countablePairLift k Q * countablePairLift k Q -
      (γ : ℂ) • countablePairLift k Q).IsPositive) :
    (countablePairLift N (countablePairConjugate countableEnvOrbital Q) *
      countablePairLift N (countablePairConjugate countableEnvOrbital Q) -
      (γ : ℂ) • countablePairLift N (countablePairConjugate countableEnvOrbital Q)).IsPositive := by
  let W := countableFockSplit.toLinearIsometry.comp (countableSector N).subtypeₗᵢ
  exact quadratic_positive_of_isometric_intertwining W _ _ γ
    (countableEnvironmentLift_identification N Q) (countableEnvironmentReference_gap N Q γ h)

/-- No enlarged reference gap is assumed: the actual loss-mode inequality
follows from CAR/frame-independent pair lifting and the constructed loss rotation. -/
theorem countableLoss_pairLift_gap
    (M : CountableOrbital →L[ℂ] CountableOrbital) (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1)
    (N : ℕ) (Q : CountablePairSpace →L[ℂ] CountablePairSpace) (γ : ℝ)
    (h : ∀ k ≤ N, (countablePairLift k Q * countablePairLift k Q -
      (γ : ℂ) • countablePairLift k Q).IsPositive) :
    (countablePairLift N (countablePairConjugate (countableLossEmbedding M hM hc) Q) *
      countablePairLift N (countablePairConjugate (countableLossEmbedding M hM hc) Q) -
      (γ : ℂ) • countablePairLift N
        (countablePairConjugate (countableLossEmbedding M hM hc) Q)).IsPositive := by
  let V := countableFockSectorEquiv (countableLossRotation M hM hc) N
  let T := countablePairLift N (countablePairConjugate (countableLossEmbedding M hM hc) Q)
  let S := countablePairLift N (countablePairConjugate countableEnvOrbital Q)
  apply quadratic_positive_of_isometric_intertwining V.symm.toLinearIsometry T S γ _
    (countableEnvironmentLift_gap N Q γ h)
  intro x
  have hh := countablePairLift_unitary_apply (countableLossRotation M hM hc) N
    (countablePairConjugate countableEnvOrbital Q) (V.symm x)
  rw [countableLoss_pair_conjugate] at hh
  change T (V (V.symm x)) = V (S (V.symm x)) at hh
  rw [V.apply_symm_apply] at hh
  have hi := congrArg V.symm hh
  simpa only [LinearIsometryEquiv.coe_toLinearIsometry, V.symm_apply_apply] using hi
end VortexGap.Fermion
