import VortexGap.Fermion.CountableVacuumLoss
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped InnerProduct

/-- One environment orbital tensored with an arbitrary completed system state,
realized inside the actual CAR representation. -/
def countableEnvironmentProduct (u : CountableOrbital) : CountableSpace →L[ℂ] CountableSpace :=
  (countableCreate (countableEnvOrbital u)).comp
    (countableFockIsometry countableSysOrbital).toContinuousLinearMap

theorem countableAnnihilate_env_system (u : CountableOrbital) (x : CountableSpace) :
    countableAnnihilate (countableEnvOrbital u) (countableFockIsometry countableSysOrbital x) = 0 := by
  rw [countableFock_annihilate_pullback, countableSysOrbital_adjoint_env]
  simp [countableAnnihilate]

theorem countableEnvironmentProduct_inner (u v : CountableOrbital) (x y : CountableSpace) :
    inner ℂ (countableEnvironmentProduct u x) (countableEnvironmentProduct v y) =
      inner ℂ u v * inner ℂ x y := by
  change inner ℂ (countableCreate (countableEnvOrbital u)
    (countableFockIsometry countableSysOrbital x))
    (countableCreate (countableEnvOrbital v) (countableFockIsometry countableSysOrbital y)) = _
  rw [countableCreate_inner, countableAnnihilate_create, countableAnnihilate_env_system,
    map_zero, sub_zero, inner_smul_right, countableEnvOrbital.inner_map_map,
    (countableFockIsometry countableSysOrbital).inner_map_map]

/-- The raw one-environment column before applying the defect. -/
def countableOneFrameCreation (M : CountableOrbital →L[ℂ] CountableOrbital)
    (u v : CountableOrbital) : CountableSpace →L[ℂ] CountableSpace :=
  (countableEnvironmentProduct u).comp (countableCreate (M v)) -
    (countableEnvironmentProduct v).comp (countableCreate (M u))

theorem countableOneFrameCreation_inner (M : CountableOrbital →L[ℂ] CountableOrbital)
    (u v s t : CountableOrbital) (x y : CountableSpace) :
    inner ℂ (countableOneFrameCreation M u v x) (countableOneFrameCreation M s t y) =
      inner ℂ u s * inner ℂ (countableCreate (M v) x) (countableCreate (M t) y) -
      inner ℂ u t * inner ℂ (countableCreate (M v) x) (countableCreate (M s) y) -
      inner ℂ v s * inner ℂ (countableCreate (M u) x) (countableCreate (M t) y) +
      inner ℂ v t * inner ℂ (countableCreate (M u) x) (countableCreate (M s) y) := by
  simp only [countableOneFrameCreation, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.comp_apply, inner_sub_left, inner_sub_right,
    countableEnvironmentProduct_inner]
  ring

theorem countableOneFrameCreation_gram (M : CountableOrbital →L[ℂ] CountableOrbital)
    (u v s t : CountableOrbital) :
    (countableOneFrameCreation M u v).adjoint.comp (countableOneFrameCreation M s t) =
      (inner ℂ u s) • (countableAnnihilate (M v) * countableCreate (M t)) -
      (inner ℂ u t) • (countableAnnihilate (M v) * countableCreate (M s)) -
      (inner ℂ v s) • (countableAnnihilate (M u) * countableCreate (M t)) +
      (inner ℂ v t) • (countableAnnihilate (M u) * countableCreate (M s)) := by
  apply ContinuousLinearMap.ext
  intro y
  apply ext_inner_left ℂ
  intro x
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    countableOneFrameCreation_inner]
  simp only [countableCreate_inner, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, inner_add_right, inner_sub_right, inner_smul_right,
    ContinuousLinearMap.mul_apply]

theorem countableFiltered_annihilate_create_norm_le
    (M : CountableOrbital →L[ℂ] CountableOrbital) (hc : ‖M‖ ≤ 1)
    (a b : CountableOrbital) (x : CountableSpace) :
    ‖countableAnnihilate (M a) (countableCreate (M b) x)‖ ≤ ‖a‖ * ‖b‖ * ‖x‖ := by
  have hm (v : CountableOrbital) : ‖M v‖ ≤ ‖v‖ := by
    simpa only [one_mul] using
      (M.le_opNorm v).trans (mul_le_mul_of_nonneg_right hc (norm_nonneg v))
  calc
    _ ≤ ‖M a‖ * ‖countableCreate (M b) x‖ := countableAnnihilate_norm_le _ _
    _ ≤ ‖M a‖ * (‖M b‖ * ‖x‖) :=
      mul_le_mul_of_nonneg_left (countableCreate_norm_le _ _) (norm_nonneg _)
    _ ≤ ‖a‖ * (‖b‖ * ‖x‖) := mul_le_mul (hm a)
      (mul_le_mul_of_nonneg_right (hm b) (norm_nonneg x))
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
    _ = _ := by ring
end VortexGap.Fermion
