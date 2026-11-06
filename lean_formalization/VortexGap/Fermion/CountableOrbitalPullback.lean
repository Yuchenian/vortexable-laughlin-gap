import VortexGap.Fermion.CountableLossRotation
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped InnerProduct ComplexConjugate ComplexOrder

theorem countableSysOrbital_adjoint_sys (v : CountableOrbital) :
    countableSysOrbital.toContinuousLinearMap.adjoint (countableSysOrbital v) = v := by
  apply ext_inner_left ℂ
  intro w
  simp only [ContinuousLinearMap.adjoint_inner_right, LinearIsometry.coe_toContinuousLinearMap]
  exact countableSysOrbital.inner_map_map w v

theorem countableEnvOrbital_adjoint_env (v : CountableOrbital) :
    countableEnvOrbital.toContinuousLinearMap.adjoint (countableEnvOrbital v) = v := by
  apply ext_inner_left ℂ
  intro w
  simp only [ContinuousLinearMap.adjoint_inner_right, LinearIsometry.coe_toContinuousLinearMap]
  exact countableEnvOrbital.inner_map_map w v

theorem countableEnvOrbital_adjoint_sys (v : CountableOrbital) :
    countableEnvOrbital.toContinuousLinearMap.adjoint (countableSysOrbital v) = 0 := by
  apply ext_inner_left ℂ
  intro w
  rw [ContinuousLinearMap.adjoint_inner_right, inner_zero_right]
  exact countableEnvSysOrbital_orthogonal w v

theorem countableSysOrbital_adjoint_env (v : CountableOrbital) :
    countableSysOrbital.toContinuousLinearMap.adjoint (countableEnvOrbital v) = 0 := by
  apply ext_inner_left ℂ
  intro w
  rw [ContinuousLinearMap.adjoint_inner_right, inner_zero_right]
  have h := congrArg conj (countableEnvSysOrbital_orthogonal v w)
  simpa only [inner_conj_symm, map_zero, LinearIsometry.coe_toContinuousLinearMap] using h

theorem countableSysOrbital_adjoint_loss
    (M : CountableOrbital →L[ℂ] CountableOrbital) (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1)
    (v : CountableOrbital) :
    countableSysOrbital.toContinuousLinearMap.adjoint (countableLossEmbedding M hM hc v) = M v := by
  rw [countableLossEmbedding_apply, map_add, countableSysOrbital_adjoint_env,
    countableSysOrbital_adjoint_sys, zero_add]

theorem countableEnvOrbital_adjoint_loss
    (M : CountableOrbital →L[ℂ] CountableOrbital) (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1)
    (v : CountableOrbital) :
    countableEnvOrbital.toContinuousLinearMap.adjoint (countableLossEmbedding M hM hc v) =
      lossDefect M v := by
  rw [countableLossEmbedding_apply, map_add, countableEnvOrbital_adjoint_env,
    countableEnvOrbital_adjoint_sys, add_zero]
end VortexGap.Fermion
