import VortexGap.Fermion.CountablePairFunctor
import VortexGap.Fermion.CountablePairAnnihilation
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped InnerProduct

def countableWedge (u v : CountableOrbital) : CountablePairSpace :=
  countablePairCoordinates (countableCreate u (countableCreate v (countableKet ∅)))

theorem countableWedge_sector (u v : CountableOrbital) :
    countableCreate u (countableCreate v (countableKet ∅)) ∈ countableSector 2 :=
  countableCreate_sector u (countableCreate_sector v (by simpa using countableKet_sector ∅))

theorem countableWedge_embed (u v : CountableOrbital) :
    countablePairEmbedding (countableWedge u v) =
      countableCreate u (countableCreate v (countableKet ∅)) :=
  countablePairEmbedding_coordinates (countableWedge_sector u v)

theorem countableWedge_map (J : CountableOrbital →ₗᵢ[ℂ] CountableOrbital) (u v : CountableOrbital) :
    countablePairMap J (countableWedge u v) = countableWedge (J u) (J v) := by
  apply countablePairEmbedding.injective
  rw [countablePairMap_embed, countableWedge_embed, countableFockIsometry_create,
    countableFockIsometry_create, countableFockIsometry_vacuum, countableWedge_embed]

theorem countableWedge_basis (a : CountablePairIndex) :
    countableWedge (orbitalKet a.val.1) (orbitalKet a.val.2) = lp.single 2 a 1 := by
  apply countablePairEmbedding.injective
  rw [countableWedge_embed, countableCreate_ket, countableCreate_ket,
    countablePairEmbedding_single, one_smul, countablePairKet, countablePairMode_adjoint]
  rfl

theorem countableWedge_anticommute (u v : CountableOrbital) :
    countableWedge u v = -countableWedge v u := by
  apply countablePairEmbedding.injective
  rw [countableWedge_embed, map_neg, countableWedge_embed]
  exact congrArg (fun T : CountableSpace →L[ℂ] CountableSpace => T (countableKet ∅))
    (countableCreate_anticommute u v)

theorem countableWedge_self (u : CountableOrbital) : countableWedge u u = 0 := by
  have h := countableWedge_anticommute u u
  have hz : (2 : ℂ) • countableWedge u u = 0 := by
    rw [two_smul]
    calc
      _ = -countableWedge u u + countableWedge u u := congrArg (fun z => z + countableWedge u u) h
      _ = 0 := neg_add_cancel _
  exact (smul_eq_zero.mp hz).resolve_left (by norm_num)

end VortexGap.Fermion
