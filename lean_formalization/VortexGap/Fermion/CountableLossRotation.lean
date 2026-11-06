import VortexGap.Fermion.CountableOrbitalJoin
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped ComplexOrder
def countableLossEmbedding (M : CountableOrbital →L[ℂ] CountableOrbital)
    (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1) : CountableOrbital →ₗᵢ[ℂ] CountableOrbital :=
  countableOrbitalJoin.toLinearIsometry.comp (lossEmbedding M hM hc)

def countableLossRotation (M : CountableOrbital →L[ℂ] CountableOrbital)
    (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1) : CountableOrbital ≃ₗᵢ[ℂ] CountableOrbital :=
  countableOrbitalJoin.symm.trans ((lossRotation M hM hc).trans countableOrbitalJoin)

theorem countableLossEmbedding_apply (M : CountableOrbital →L[ℂ] CountableOrbital)
    (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1) (v : CountableOrbital) :
    countableLossEmbedding M hM hc v =
      countableEnvOrbital (lossDefect M v) + countableSysOrbital (M v) := rfl

theorem countableLossRotation_join (M : CountableOrbital →L[ℂ] CountableOrbital)
    (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1) (z : Doubled CountableOrbital) :
    countableLossRotation M hM hc (countableOrbitalJoin z) =
      countableOrbitalJoin (lossRotation M hM hc z) := by
  change countableOrbitalJoin (lossRotation M hM hc
    (countableOrbitalJoin.symm (countableOrbitalJoin z))) = _
  rw [countableOrbitalJoin.symm_apply_apply]

theorem countableLossRotation_env (M : CountableOrbital →L[ℂ] CountableOrbital)
    (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1) (v : CountableOrbital) :
    countableLossRotation M hM hc (countableEnvOrbital v) = countableLossEmbedding M hM hc v := by
  have h : countableOrbitalJoin (WithLp.toLp 2 (v,(0 : CountableOrbital))) =
      countableEnvOrbital v := by rw [countableOrbitalJoin_apply, map_zero, add_zero]
  rw [← h, countableLossRotation_join, lossRotation_first_axis]
  rfl

theorem countableLossRotation_square (M : CountableOrbital →L[ℂ] CountableOrbital)
    (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1) (v : CountableOrbital) :
    countableLossRotation M hM hc (countableLossRotation M hM hc v) = v := by
  obtain ⟨z,rfl⟩ := countableOrbitalJoin.surjective v
  rw [countableLossRotation_join, countableLossRotation_join]
  change countableOrbitalJoin (lossRotationLinear M (lossRotationLinear M z)) = _
  rw [lossRotation_involutive M hM hc]

end VortexGap.Fermion
