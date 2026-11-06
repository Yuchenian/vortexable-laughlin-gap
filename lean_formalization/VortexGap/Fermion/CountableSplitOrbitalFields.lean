import VortexGap.Fermion.CountableSplitTensorFields
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped BigOperators
theorem countableOrbital_clm_ext {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (S T : CountableOrbital →L[ℂ] E) (h : ∀ j, S (orbitalKet j) = T (orbitalKet j)) :
    S = T := by
  ext v
  have hs := (orbital_hasSum v).map S.toAddMonoidHom S.continuous
  have ht := (orbital_hasSum v).map T.toAddMonoidHom T.continuous
  change HasSum (fun j => S (v j • orbitalKet j)) (S v) at hs
  change HasSum (fun j => T (v j • orbitalKet j)) (T v) at ht
  simp only [map_smul, h] at hs
  simp only [map_smul] at ht
  exact hs.unique ht

theorem countableSplit_create_sys_orbital_coordinate
    (v : CountableOrbital) (x : CountableSplitSpace) (A B : Finset ℕ) :
    countableSplitConjugate (countableCreate (countableSysOrbital v)) x (A,B) =
      ((-1 : ℂ)^A.card) * (countableCreate v (l2ProductFiber x A)) B := by
  let L : CountableOrbital →L[ℂ] ℂ :=
    (lp.evalCLM ℂ _ 2 (A,B)).comp
      (countableFockSplit.toLinearIsometry.toContinuousLinearMap.comp
        ((ContinuousLinearMap.apply ℂ CountableSpace (countableFockJoin x)).comp
          (countableCreate.comp countableSysOrbital.toContinuousLinearMap)))
  let R : CountableOrbital →L[ℂ] ℂ :=
    ((-1 : ℂ)^A.card) • ((lp.evalCLM ℂ _ 2 B).comp
      ((ContinuousLinearMap.apply ℂ CountableSpace (l2ProductFiber x A)).comp countableCreate))
  have h : L = R := by
    apply countableOrbital_clm_ext
    intro j
    change countableSplitConjugate (countableCreate (countableSysOrbital (orbitalKet j))) x (A,B) =
      ((-1 : ℂ)^A.card) * (countableCreate (orbitalKet j) (l2ProductFiber x A)) B
    rw [countableSysOrbital_ket, countableCreate_ket]
    exact congrArg (fun y : CountableSpace => y B) (countableSplit_create_sys_fiber j x A)
  exact congrArg (fun T : CountableOrbital →L[ℂ] ℂ => T v) h
theorem countableOrbital_antilinear_ext {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (S T : CountableOrbital →L⋆[ℂ] E) (h : ∀ j, S (orbitalKet j) = T (orbitalKet j)) :
    S = T := by
  ext v
  have hs := (orbital_hasSum v).map S.toAddMonoidHom S.continuous
  have ht := (orbital_hasSum v).map T.toAddMonoidHom T.continuous
  change HasSum (fun j => S (v j • orbitalKet j)) (S v) at hs
  change HasSum (fun j => T (v j • orbitalKet j)) (T v) at ht
  simp only [map_smulₛₗ, h] at hs
  simp only [map_smulₛₗ] at ht
  exact hs.unique ht

theorem countableSplit_annihilate_sys_orbital_coordinate
    (v : CountableOrbital) (x : CountableSplitSpace) (A B : Finset ℕ) :
    countableSplitConjugate (countableAnnihilate (countableSysOrbital v)) x (A,B) =
      ((-1 : ℂ)^A.card) * (countableAnnihilate v (l2ProductFiber x A)) B := by
  let L : CountableOrbital →L⋆[ℂ] ℂ :=
    (lp.evalCLM ℂ _ 2 (A,B)).comp
      (countableFockSplit.toLinearIsometry.toContinuousLinearMap.comp
        ((ContinuousLinearMap.apply ℂ CountableSpace (countableFockJoin x)).comp
          (ContinuousLinearMap.adjoint.toLinearIsometry.toContinuousLinearMap.comp (countableCreate.comp countableSysOrbital.toContinuousLinearMap))))
  let R : CountableOrbital →L⋆[ℂ] ℂ :=
    ((-1 : ℂ)^A.card) • ((lp.evalCLM ℂ _ 2 B).comp
      ((ContinuousLinearMap.apply ℂ CountableSpace (l2ProductFiber x A)).comp (ContinuousLinearMap.adjoint.toLinearIsometry.toContinuousLinearMap.comp countableCreate)))
  have h : L = R := by
    apply countableOrbital_antilinear_ext
    intro j
    change countableSplitConjugate (countableAnnihilate (countableSysOrbital (orbitalKet j))) x (A,B) =
      ((-1 : ℂ)^A.card) * (countableAnnihilate (orbitalKet j) (l2ProductFiber x A)) B
    rw [countableSysOrbital_ket, countableAnnihilate_ket]
    exact congrArg (fun y : CountableSpace => y B) (countableSplit_annihilate_sys_fiber j x A)
  exact congrArg (fun T : CountableOrbital →L⋆[ℂ] ℂ => T v) h


theorem countableSplit_create_sys_orbital_fiber (v : CountableOrbital) (x : CountableSplitSpace) (A : Finset ℕ) :
    l2ProductFiber (countableSplitConjugate (countableCreate (countableSysOrbital v)) x) A =
      ((-1 : ℂ)^A.card) • countableCreate v (l2ProductFiber x A) := by
  ext B
  exact countableSplit_create_sys_orbital_coordinate v x A B


theorem countableSplit_annihilate_sys_orbital_fiber (v : CountableOrbital) (x : CountableSplitSpace) (A : Finset ℕ) :
    l2ProductFiber (countableSplitConjugate (countableAnnihilate (countableSysOrbital v)) x) A =
      ((-1 : ℂ)^A.card) • countableAnnihilate v (l2ProductFiber x A) := by
  ext B
  exact countableSplit_annihilate_sys_orbital_coordinate v x A B

end VortexGap.Fermion
