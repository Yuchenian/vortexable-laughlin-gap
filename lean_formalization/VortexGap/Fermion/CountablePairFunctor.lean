import VortexGap.Fermion.CountablePairSpace
import VortexGap.Fermion.CountableFockFunctor
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
def countablePairMap (J : CountableOrbital →ₗᵢ[ℂ] CountableOrbital) :
    CountablePairSpace →L[ℂ] CountablePairSpace :=
  countablePairCoordinates.comp ((countableFockIsometry J).toContinuousLinearMap.comp
    countablePairEmbedding.toContinuousLinearMap)

theorem countablePairMap_embed (J : CountableOrbital →ₗᵢ[ℂ] CountableOrbital) (p : CountablePairSpace) :
    countablePairEmbedding (countablePairMap J p) =
      countableFockIsometry J (countablePairEmbedding p) :=
  countablePairEmbedding_coordinates (countableFockIsometry_sector J (countablePairEmbedding_sector p))

theorem countablePairMap_norm (J : CountableOrbital →ₗᵢ[ℂ] CountableOrbital) (p : CountablePairSpace) :
    ‖countablePairMap J p‖ = ‖p‖ := by
  rw [← countablePairEmbedding.norm_map, countablePairMap_embed,
    (countableFockIsometry J).norm_map, countablePairEmbedding.norm_map]

theorem countablePairMap_comp (J K : CountableOrbital →ₗᵢ[ℂ] CountableOrbital) (p : CountablePairSpace) :
    countablePairMap J (countablePairMap K p) = countablePairMap (J.comp K) p := by
  apply countablePairEmbedding.injective
  rw [countablePairMap_embed, countablePairMap_embed, countablePairMap_embed,
    countableFockIsometry_comp_apply]

theorem countablePairMap_id (p : CountablePairSpace) :
    countablePairMap LinearIsometry.id p = p := by
  apply countablePairEmbedding.injective
  rw [countablePairMap_embed, countableFockIsometry_id]
  rfl

def countablePairIsometry (J : CountableOrbital →ₗᵢ[ℂ] CountableOrbital) :
    CountablePairSpace →ₗᵢ[ℂ] CountablePairSpace :=
  ⟨(countablePairMap J).toLinearMap, countablePairMap_norm J⟩
end VortexGap.Fermion
