import VortexGap.Fermion.CountableWedge
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped InnerProduct

theorem countableWedge_inner (u v s t : CountableOrbital) :
    inner ℂ (countableWedge u v) (countableWedge s t) =
      inner ℂ u s * inner ℂ v t - inner ℂ u t * inner ℂ v s := by
  rw [← countablePairEmbedding.inner_map_map, countableWedge_embed, countableWedge_embed,
    countableCreate_inner, countableAnnihilate_create, countableAnnihilate_create_vacuum,
    inner_sub_right]
  simp only [map_smul, inner_smul_right, countableCreate_inner,
    countableAnnihilate_create_vacuum, countableKet_inner]
  simp

theorem countableWedge_coordinate (u v : CountableOrbital) (a : CountablePairIndex) :
    countableWedge u v a = u a.val.1 * v a.val.2 - v a.val.1 * u a.val.2 := by
  have h := countableWedge_inner (orbitalKet a.val.1) (orbitalKet a.val.2) u v
  rw [countableWedge_basis, lp.inner_single_left] at h
  simpa [RCLike.inner_apply, orbitalKet_inner_left, mul_comm] using h

end VortexGap.Fermion
