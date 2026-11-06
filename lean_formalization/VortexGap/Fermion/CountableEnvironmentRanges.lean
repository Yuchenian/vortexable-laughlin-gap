import VortexGap.Fermion.CountablePairEnvironment
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped InnerProduct

theorem countableSingleParticle_sector (u : CountableOrbital) :
    countableSingleParticle u ∈ countableSector 1 := by
  exact countableCreate_sector u (by simpa using countableKet_sector ∅)

theorem countableOneEnvironmentAction_sector
    (T : CountableOrbital →L[ℂ] CountableOrbital) (x : CountableSpace) :
    countableFockSplit (countableOneEnvironmentAction T x) ∈ countableEnvironmentSector 1 := by
  intro AB hAB
  rcases AB with ⟨A,B⟩
  change countableFockSplit (countableFockJoin
    (countableEnvironmentAmplify (countableSingleAction T) (countableFockSplit x))) (A,B) = 0
  rw [countableFockSplit, countableFockJoin.symm_apply_apply, countableEnvironmentAmplify_apply]
  exact countableSingleParticle_sector
    (T (countableSingleParticle.toContinuousLinearMap.adjoint
      (countableEnvironmentFiber (countableFockSplit x) B))) A hAB

theorem countablePairEnvironmentEmbed_sector (z : CountablePairStackSpace) :
    countableFockSplit (countablePairEnvironmentEmbed z) ∈ countableEnvironmentSector 2 := by
  intro AB hAB
  rcases AB with ⟨A,B⟩
  change countableEnvironmentFiber (countableFockSplit (countablePairEnvironmentEmbed z)) B A = 0
  rw [countablePairEnvironmentEmbed_fiber]
  exact countablePairEmbedding_sector (countablePairFiber z B) A hAB

theorem countableVacuum_oneEnvironment_orthogonal
    (T : CountableOrbital →L[ℂ] CountableOrbital) (x y : CountableSpace) :
    inner ℂ (countableFockIsometry countableSysOrbital x) (countableOneEnvironmentAction T y) = 0 := by
  rw [← countableFockSplit.inner_map_map]
  apply countableEnvironmentSector_orthogonal (K := 0) (L := 1)
  · rw [countableFockSplit_system]
    exact countableVacuumTensor_environment x
  · exact countableOneEnvironmentAction_sector T y
  · decide

theorem countableVacuum_pairEnvironment_orthogonal
    (x : CountableSpace) (z : CountablePairStackSpace) :
    inner ℂ (countableFockIsometry countableSysOrbital x) (countablePairEnvironmentEmbed z) = 0 := by
  rw [← countableFockSplit.inner_map_map]
  apply countableEnvironmentSector_orthogonal (K := 0) (L := 2)
  · rw [countableFockSplit_system]
    exact countableVacuumTensor_environment x
  · exact countablePairEnvironmentEmbed_sector z
  · decide

theorem countableOne_pairEnvironment_orthogonal
    (T : CountableOrbital →L[ℂ] CountableOrbital) (y : CountableSpace) (z : CountablePairStackSpace) :
    inner ℂ (countableOneEnvironmentAction T y) (countablePairEnvironmentEmbed z) = 0 := by
  rw [← countableFockSplit.inner_map_map]
  exact countableEnvironmentSector_orthogonal
    (countableOneEnvironmentAction_sector T y) (countablePairEnvironmentEmbed_sector z) (by decide)

/-- Orthogonal norm decomposition for the actual vacuum, one- and two-environment ranges. -/
theorem countableEnvironmentOutputs_norm_sq
    (T : CountableOrbital →L[ℂ] CountableOrbital) (x y : CountableSpace) (z : CountablePairStackSpace) :
    ‖countableFockIsometry countableSysOrbital x + countableOneEnvironmentAction T y +
      countablePairEnvironmentEmbed z‖^2 =
      ‖x‖^2 + ‖countableOneEnvironmentAction T y‖^2 + ‖countablePairEnvironmentEmbed z‖^2 := by
  simp only [pow_two]
  rw [norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ) _ _ (by
    rw [inner_add_left, countableVacuum_pairEnvironment_orthogonal,
      countableOne_pairEnvironment_orthogonal, add_zero])]
  rw [norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ) _ _
    (countableVacuum_oneEnvironment_orthogonal T x y)]
  rw [(countableFockIsometry countableSysOrbital).norm_map]

theorem countableEnvironmentOutputs_inner
    (T : CountableOrbital →L[ℂ] CountableOrbital) (x h y : CountableSpace) (z : CountablePairStackSpace) :
    inner ℂ (countableFockIsometry countableSysOrbital x)
      (countableFockIsometry countableSysOrbital h + countableOneEnvironmentAction T y +
        countablePairEnvironmentEmbed z) = inner ℂ x h := by
  rw [inner_add_right, inner_add_right, countableVacuum_oneEnvironment_orthogonal,
    countableVacuum_pairEnvironment_orthogonal,
    (countableFockIsometry countableSysOrbital).inner_map_map]
  simp only [add_zero]

end VortexGap.Fermion
