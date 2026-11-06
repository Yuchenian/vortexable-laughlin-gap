import VortexGap.Fermion.CountablePairCompression
import VortexGap.Fermion.CountableOneEnvironment
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped InnerProduct

/-- Embed the completed pair/system Hilbert sum into the physical doubled Fock
space, placing the pair in the environment. -/
def countablePairEnvironmentEmbed : CountablePairStackSpace →L[ℂ] CountableSpace :=
  countableFockJoin.toLinearIsometry.toContinuousLinearMap.comp
    (countableSplitExchange.toLinearIsometry.toContinuousLinearMap.comp
      ((l2Curry (Finset ℕ) (Finset ℕ)).symm.toLinearIsometry.toContinuousLinearMap.comp
        ((lp.mapCLM 2 (fun _ : Finset ℕ => countablePairEmbedding.toContinuousLinearMap)
          (by norm_num : (0 : ℝ) ≤ 1)
          (fun _ => countablePairEmbedding.norm_toContinuousLinearMap_le)).comp
            (l2Exchange CountablePairIndex (Finset ℕ)).toLinearIsometry.toContinuousLinearMap)))

theorem countablePairEnvironmentEmbed_norm_le (z : CountablePairStackSpace) :
    ‖countablePairEnvironmentEmbed z‖ ≤ ‖z‖ := by
  change ‖countableFockJoin (countableSplitExchange
    ((l2Curry (Finset ℕ) (Finset ℕ)).symm
      (lp.mapCLM 2 (fun _ : Finset ℕ => countablePairEmbedding.toContinuousLinearMap)
        (by norm_num : (0 : ℝ) ≤ 1)
        (fun _ => countablePairEmbedding.norm_toContinuousLinearMap_le)
        (l2Exchange CountablePairIndex (Finset ℕ) z))))‖ ≤ _
  rw [countableFockJoin.norm_map, countableSplitExchange.norm_map,
    (l2Curry (Finset ℕ) (Finset ℕ)).symm.norm_map]
  have h := (lp.mapCLM 2 (fun _ : Finset ℕ => countablePairEmbedding.toContinuousLinearMap)
    (by norm_num : (0 : ℝ) ≤ 1)
    (fun _ => countablePairEmbedding.norm_toContinuousLinearMap_le)).le_of_opNorm_le
    (lp.norm_mapCLM_le 2 _ (by norm_num : (0 : ℝ) ≤ 1)
      (fun _ => countablePairEmbedding.norm_toContinuousLinearMap_le))
      (l2Exchange CountablePairIndex (Finset ℕ) z)
  simpa only [one_mul, (l2Exchange CountablePairIndex (Finset ℕ)).norm_map] using h

theorem countablePairEnvironmentEmbed_fiber (z : CountablePairStackSpace) (B : Finset ℕ) :
    countableEnvironmentFiber (countableFockSplit (countablePairEnvironmentEmbed z)) B =
      countablePairEmbedding (countablePairFiber z B) := by
  ext A
  change countableFockJoin.symm (countableFockJoin _) (A,B) = _
  rw [countableFockJoin.symm_apply_apply]
  rfl

theorem countableEnvironment_create_fiber (u : CountableOrbital) (x : CountableSpace)
    (B : Finset ℕ) :
    countableEnvironmentFiber (countableFockSplit (countableCreate (countableEnvOrbital u) x)) B =
      countableCreate u (countableEnvironmentFiber (countableFockSplit x) B) := by
  ext A
  simpa only [countableEnvironmentFiber_apply, countableSplitConjugate_apply, countableFockSplit,
    countableFockJoin.apply_symm_apply] using
    countableSplit_create_env_orbital_coordinate u (countableFockSplit x) A B

theorem countablePairEnvironmentEmbed_wedge (u v : CountableOrbital) (x : CountableSpace) :
    countablePairEnvironmentEmbed (countablePairTensor (countableWedge u v) x) =
      countableCreate (countableEnvOrbital u)
        (countableCreate (countableEnvOrbital v) (countableFockIsometry countableSysOrbital x)) := by
  apply countableFockSplit.injective
  ext AB
  rcases AB with ⟨A,B⟩
  change countableEnvironmentFiber (countableFockSplit
    (countablePairEnvironmentEmbed (countablePairTensor (countableWedge u v) x))) B A =
    countableEnvironmentFiber (countableFockSplit
      (countableCreate (countableEnvOrbital u)
        (countableCreate (countableEnvOrbital v) (countableFockIsometry countableSysOrbital x)))) B A
  rw [countablePairEnvironmentEmbed_fiber, countablePairTensor_fiber, map_smul,
    countableWedge_embed, countableEnvironment_create_fiber, countableEnvironment_create_fiber,
    countableFockSplit_system, countableVacuumTensor_environmentFiber, map_smul, map_smul]

theorem countableLossCreationTwo_factorization
    (M : CountableOrbital →L[ℂ] CountableOrbital) (u v : CountableOrbital) (x : CountableSpace) :
    countableLossCreationTwo M u v x = countablePairEnvironmentEmbed
      (countablePairAmplify (countablePairFilter (lossDefect M) (lossDefect_nonneg M))
        (countablePairTensor (countableWedge u v) x)) := by
  rw [countablePairAmplify_tensor, countablePairFilter_wedge, countablePairEnvironmentEmbed_wedge]
  rfl
end VortexGap.Fermion
