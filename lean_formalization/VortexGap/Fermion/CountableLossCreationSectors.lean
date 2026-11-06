import VortexGap.Fermion.CountableLossCreation
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped InnerProduct ComplexOrder

theorem countableEnvironmentCreation_sector {K : ℕ} (v : CountableOrbital)
    {x : CountableSpace} (hx : countableFockSplit x ∈ countableEnvironmentSector K) :
    countableFockSplit (countableCreate (countableEnvOrbital v) x) ∈
      countableEnvironmentSector (K+1) := by
  intro AB hAB
  rcases AB with ⟨A,B⟩
  have hf : countableEnvironmentFiber (countableFockSplit x) B ∈ countableSector K := by
    intro C hC
    exact hx (C,B) hC
  have hcoord : countableFockSplit (countableCreate (countableEnvOrbital v) x) (A,B) =
      countableCreate v (countableEnvironmentFiber (countableFockSplit x) B) A := by
    simpa only [countableSplitConjugate_apply, countableFockSplit,
      countableFockJoin.apply_symm_apply] using
      countableSplit_create_env_orbital_coordinate v (countableFockSplit x) A B
  rw [hcoord]
  exact (countableCreate_sector v hf) A hAB

theorem countableLossCreationZero_sector
    (M : CountableOrbital →L[ℂ] CountableOrbital) (u v : CountableOrbital) (x : CountableSpace) :
    countableFockSplit (countableLossCreationZero M u v x) ∈ countableEnvironmentSector 0 := by
  change countableFockSplit (countableFockIsometry countableSysOrbital _) ∈ _
  rw [countableFockSplit_system]
  exact countableVacuumTensor_environment _

theorem countableLossCreationOne_sector
    (M : CountableOrbital →L[ℂ] CountableOrbital) (u v : CountableOrbital) (x : CountableSpace) :
    countableFockSplit (countableLossCreationOne M u v x) ∈ countableEnvironmentSector 1 := by
  change countableFockSplit
    (countableCreate (countableEnvOrbital (lossDefect M u))
      (countableFockIsometry countableSysOrbital (countableCreate (M v) x)) -
     countableCreate (countableEnvOrbital (lossDefect M v))
      (countableFockIsometry countableSysOrbital (countableCreate (M u) x))) ∈ _
  rw [map_sub]
  apply (countableEnvironmentSector 1).sub_mem
  · apply countableEnvironmentCreation_sector
    rw [countableFockSplit_system]
    exact countableVacuumTensor_environment _
  · apply countableEnvironmentCreation_sector
    rw [countableFockSplit_system]
    exact countableVacuumTensor_environment _

theorem countableLossCreationTwo_sector
    (M : CountableOrbital →L[ℂ] CountableOrbital) (u v : CountableOrbital) (x : CountableSpace) :
    countableFockSplit (countableLossCreationTwo M u v x) ∈ countableEnvironmentSector 2 := by
  change countableFockSplit (countableCreate (countableEnvOrbital (lossDefect M u))
    (countableCreate (countableEnvOrbital (lossDefect M v))
      (countableFockIsometry countableSysOrbital x))) ∈ _
  apply countableEnvironmentCreation_sector
  apply countableEnvironmentCreation_sector
  rw [countableFockSplit_system]
  exact countableVacuumTensor_environment _

theorem countableLossCreation_orthogonal
    (M : CountableOrbital →L[ℂ] CountableOrbital) (u v : CountableOrbital) (x y : CountableSpace) :
    inner ℂ (countableLossCreationZero M u v x) (countableLossCreationOne M u v y) = 0 ∧
    inner ℂ (countableLossCreationZero M u v x) (countableLossCreationTwo M u v y) = 0 ∧
    inner ℂ (countableLossCreationOne M u v x) (countableLossCreationTwo M u v y) = 0 := by
  constructor
  · rw [← countableFockSplit.inner_map_map]
    exact countableEnvironmentSector_orthogonal
      (countableLossCreationZero_sector M u v x) (countableLossCreationOne_sector M u v y) (by decide)
  constructor
  · rw [← countableFockSplit.inner_map_map]
    exact countableEnvironmentSector_orthogonal
      (countableLossCreationZero_sector M u v x) (countableLossCreationTwo_sector M u v y) (by decide)
  · rw [← countableFockSplit.inner_map_map]
    exact countableEnvironmentSector_orthogonal
      (countableLossCreationOne_sector M u v x) (countableLossCreationTwo_sector M u v y) (by decide)

theorem countableLoss_creation_norm_sq
    (M : CountableOrbital →L[ℂ] CountableOrbital) (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1)
    (u v : CountableOrbital) (x : CountableSpace) :
    ‖countableCreate (countableLossEmbedding M hM hc u)
      (countableCreate (countableLossEmbedding M hM hc v)
        (countableFockIsometry countableSysOrbital x))‖^2 =
    ‖countableLossCreationZero M u v x‖^2 + ‖countableLossCreationOne M u v x‖^2 +
      ‖countableLossCreationTwo M u v x‖^2 := by
  obtain ⟨h01,h02,h12⟩ := countableLossCreation_orthogonal M u v x x
  rw [countableLoss_creation_output]
  simp only [pow_two]
  rw [norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ) _ _ (by
      rw [inner_add_left, h02, h12, add_zero]),
    norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ) _ _ h01]
end VortexGap.Fermion
