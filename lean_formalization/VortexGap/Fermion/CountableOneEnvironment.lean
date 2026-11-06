import VortexGap.Fermion.CountableOneFrame
import VortexGap.Fermion.CountableLossCreation
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped InnerProduct

/-- The actual one-particle sector embedding, given by creation on vacuum. -/
def countableSingleParticle : CountableOrbital →ₗᵢ[ℂ] CountableSpace where
  toLinearMap := ((ContinuousLinearMap.apply ℂ CountableSpace (countableKet ∅)).comp
    countableCreate).toLinearMap
  norm_map' := countableCreate_vacuum_norm

theorem countableSingleParticle_apply (u : CountableOrbital) :
    countableSingleParticle u = countableCreate u (countableKet ∅) := rfl

/-- Extend a one-particle operator by zero outside the one-particle sector. -/
def countableSingleAction (T : CountableOrbital →L[ℂ] CountableOrbital) :
    CountableSpace →L[ℂ] CountableSpace :=
  countableSingleParticle.toContinuousLinearMap.comp
    (T.comp countableSingleParticle.toContinuousLinearMap.adjoint)

theorem countableSingleAction_apply (T : CountableOrbital →L[ℂ] CountableOrbital)
    (u : CountableOrbital) :
    countableSingleAction T (countableSingleParticle u) = countableSingleParticle (T u) := by
  have h := congrArg (fun A : CountableOrbital →L[ℂ] CountableOrbital => A u)
    countableSingleParticle.adjoint_comp_self
  change countableSingleParticle.toContinuousLinearMap.adjoint (countableSingleParticle u) = u at h
  change countableSingleParticle (T (countableSingleParticle.toContinuousLinearMap.adjoint
    (countableSingleParticle u))) = _
  rw [h]

theorem countableSingleAction_norm_le (T : CountableOrbital →L[ℂ] CountableOrbital) :
    ‖countableSingleAction T‖ ≤ ‖T‖ := by
  have hi := countableSingleParticle.norm_toContinuousLinearMap_le
  have ha : ‖countableSingleParticle.toContinuousLinearMap.adjoint‖ ≤ 1 := by
    rwa [ContinuousLinearMap.adjoint.norm_map]
  calc
    _ ≤ ‖countableSingleParticle.toContinuousLinearMap‖ *
        ‖T.comp countableSingleParticle.toContinuousLinearMap.adjoint‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * (‖T‖ * 1) := mul_le_mul hi
      ((ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left ha (norm_nonneg T))) (norm_nonneg _) (by norm_num)
    _ = _ := by ring

theorem countableVacuumTensor_environmentFiber (x : CountableSpace) (B : Finset ℕ) :
    countableEnvironmentFiber (countableVacuumTensor x) B = x B • countableKet ∅ := by
  ext A
  rw [countableEnvironmentFiber_apply, countableVacuumTensor_coordinate]
  by_cases h : A = ∅
  · subst A
    simp [countableKet, lp.single_apply]
  · simp [countableKet, lp.single_apply, h, Ne.symm h]

theorem countableEnvironmentProduct_fiber (u : CountableOrbital) (x : CountableSpace)
    (B : Finset ℕ) :
    countableEnvironmentFiber (countableFockSplit (countableEnvironmentProduct u x)) B =
      x B • countableSingleParticle u := by
  have h : countableFockSplit (countableEnvironmentProduct u x) =
      countableEnvironmentAmplify (countableCreate u) (countableVacuumTensor x) := by
    rw [← countableFockSplit_system, ← countableSplit_create_env_tensor]
    simp only [countableSplitConjugate_apply, countableFockSplit,
      countableFockJoin.apply_symm_apply]
    rfl
  rw [h, countableEnvironmentAmplify_fiber, countableVacuumTensor_environmentFiber, map_smul]
  rfl

/-- The bounded action on one environment particle, with an untouched system spectator. -/
def countableOneEnvironmentAction (T : CountableOrbital →L[ℂ] CountableOrbital) :
    CountableSpace →L[ℂ] CountableSpace :=
  countableFockJoin.toLinearIsometry.toContinuousLinearMap.comp
    ((countableEnvironmentAmplify (countableSingleAction T)).comp
      countableFockSplit.toLinearIsometry.toContinuousLinearMap)

theorem countableOneEnvironmentAction_product (T : CountableOrbital →L[ℂ] CountableOrbital)
    (u : CountableOrbital) (x : CountableSpace) :
    countableOneEnvironmentAction T (countableEnvironmentProduct u x) =
      countableEnvironmentProduct (T u) x := by
  apply countableFockSplit.injective
  change countableFockSplit (countableFockJoin _) = _
  rw [countableFockSplit, countableFockJoin.symm_apply_apply]
  ext AB
  rcases AB with ⟨A,B⟩
  change countableEnvironmentAmplify (countableSingleAction T)
    (countableFockSplit (countableEnvironmentProduct u x)) (A,B) = _
  rw [countableEnvironmentAmplify_apply, countableEnvironmentProduct_fiber, map_smul,
    countableSingleAction_apply]
  exact congrArg (fun y : CountableSpace => y A)
    (countableEnvironmentProduct_fiber (T u) x B).symm

theorem countableOneEnvironmentAction_norm_le (T : CountableOrbital →L[ℂ] CountableOrbital)
    (x : CountableSpace) :
    ‖countableOneEnvironmentAction T x‖ ≤ ‖T‖ * ‖x‖ := by
  change ‖countableFockJoin (countableEnvironmentAmplify (countableSingleAction T)
    (countableFockSplit x))‖ ≤ _
  rw [countableFockJoin.norm_map]
  exact (countableEnvironmentAmplify_norm_le _ _).trans
    (by rw [countableFockSplit.norm_map]
        exact mul_le_mul_of_nonneg_right (countableSingleAction_norm_le T) (norm_nonneg x))

theorem countableLossCreationOne_factorization
    (M : CountableOrbital →L[ℂ] CountableOrbital) (u v : CountableOrbital) (x : CountableSpace) :
    countableLossCreationOne M u v x =
      countableOneEnvironmentAction (lossDefect M) (countableOneFrameCreation M u v x) := by
  simp only [countableOneFrameCreation, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.comp_apply, map_sub, countableOneEnvironmentAction_product]
  rfl
end VortexGap.Fermion
