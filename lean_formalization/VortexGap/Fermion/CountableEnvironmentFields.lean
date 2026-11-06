import VortexGap.Fermion.CountableEnvironmentAmplification
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
theorem countableSplit_create_env_orbital_coordinate
    (v : CountableOrbital) (x : CountableSplitSpace) (A B : Finset ℕ) :
    countableSplitConjugate (countableCreate (countableEnvOrbital v)) x (A,B) =
      (countableCreate v (countableEnvironmentFiber x B)) A := by
  let L : CountableOrbital →L[ℂ] ℂ :=
    (lp.evalCLM ℂ _ 2 (A,B)).comp
      (countableFockSplit.toLinearIsometry.toContinuousLinearMap.comp
        ((ContinuousLinearMap.apply ℂ CountableSpace (countableFockJoin x)).comp
          (countableCreate.comp countableEnvOrbital.toContinuousLinearMap)))
  let R : CountableOrbital →L[ℂ] ℂ :=
    ((lp.evalCLM ℂ _ 2 A).comp
      ((ContinuousLinearMap.apply ℂ CountableSpace (countableEnvironmentFiber x B)).comp countableCreate))
  have h : L = R := by
    apply countableOrbital_clm_ext
    intro j
    change countableSplitConjugate (countableCreate (countableEnvOrbital (orbitalKet j))) x (A,B) =
      (countableCreate (orbitalKet j) (countableEnvironmentFiber x B)) A
    rw [countableEnvOrbital_ket, countableCreate_ket]
    exact congrArg (fun y : CountableSpace => y A) (countableSplit_create_env_fiber j x B)
  exact congrArg (fun T : CountableOrbital →L[ℂ] ℂ => T v) h
theorem countableSplit_annihilate_env_orbital_coordinate
    (v : CountableOrbital) (x : CountableSplitSpace) (A B : Finset ℕ) :
    countableSplitConjugate (countableAnnihilate (countableEnvOrbital v)) x (A,B) =
      (countableAnnihilate v (countableEnvironmentFiber x B)) A := by
  let L : CountableOrbital →L⋆[ℂ] ℂ :=
    (lp.evalCLM ℂ _ 2 (A,B)).comp
      (countableFockSplit.toLinearIsometry.toContinuousLinearMap.comp
        ((ContinuousLinearMap.apply ℂ CountableSpace (countableFockJoin x)).comp
          (ContinuousLinearMap.adjoint.toLinearIsometry.toContinuousLinearMap.comp (countableCreate.comp countableEnvOrbital.toContinuousLinearMap))))
  let R : CountableOrbital →L⋆[ℂ] ℂ :=
    ((lp.evalCLM ℂ _ 2 A).comp
      ((ContinuousLinearMap.apply ℂ CountableSpace (countableEnvironmentFiber x B)).comp (ContinuousLinearMap.adjoint.toLinearIsometry.toContinuousLinearMap.comp countableCreate)))
  have h : L = R := by
    apply countableOrbital_antilinear_ext
    intro j
    change countableSplitConjugate (countableAnnihilate (countableEnvOrbital (orbitalKet j))) x (A,B) =
      (countableAnnihilate (orbitalKet j) (countableEnvironmentFiber x B)) A
    rw [countableEnvOrbital_ket, countableAnnihilate_ket]
    exact congrArg (fun y : CountableSpace => y A) (countableSplit_annihilate_env_fiber j x B)
  exact congrArg (fun T : CountableOrbital →L⋆[ℂ] ℂ => T v) h

theorem countableSplit_create_env_tensor (v : CountableOrbital) :
    countableSplitConjugate (countableCreate (countableEnvOrbital v)) =
      countableEnvironmentAmplify (countableCreate v) := by
  ext x AB
  exact countableSplit_create_env_orbital_coordinate v x AB.1 AB.2


theorem countableSplit_annihilate_env_tensor (v : CountableOrbital) :
    countableSplitConjugate (countableAnnihilate (countableEnvOrbital v)) =
      countableEnvironmentAmplify (countableAnnihilate v) := by
  ext x AB
  exact countableSplit_annihilate_env_orbital_coordinate v x AB.1 AB.2

end VortexGap.Fermion
