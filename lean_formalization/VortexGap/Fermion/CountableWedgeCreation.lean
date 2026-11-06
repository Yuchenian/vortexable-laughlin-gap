import VortexGap.Fermion.CountableLossCreationSectors
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped InnerProduct

theorem countablePairAnnihilate_wedge_adjoint {N : ℕ}
    (u v : CountableOrbital) (x : countableSector N) :
    (countablePairAnnihilate (N+2) (countableWedge u v)).adjoint (x : CountableSpace) =
      ⟨countableCreate u (countableCreate v x),
        countableCreate_sector u (countableCreate_sector v x.property)⟩ := by
  apply ext_inner_left ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_right, countablePairAnnihilate_wedge]
  change inner ℂ (countableAnnihilate v (countableAnnihilate u y)) (x : CountableSpace) =
    inner ℂ (y : CountableSpace) (countableCreate u (countableCreate v x))
  rw [countableAnnihilate_inner, countableAnnihilate_inner]

theorem countablePairLift_wedge_rankOne {N : ℕ}
    (u v s t : CountableOrbital) (x : countableSector (N+2)) :
    (countablePairLift (N+2) (InnerProductSpace.rankOne ℂ
      (countableWedge u v) (countableWedge s t)) x : CountableSpace) =
    countableCreate u (countableCreate v
      (countableAnnihilate t (countableAnnihilate s x))) := by
  rw [countablePairLift_rankOne, ContinuousLinearMap.comp_apply]
  let y : countableSector N := ⟨countablePairAnnihilate (N+2) (countableWedge s t) x,
    countablePairAnnihilate_sector (countableWedge s t) x⟩
  have h := congrArg (fun z : countableSector (N+2) => (z : CountableSpace))
    (countablePairAnnihilate_wedge_adjoint u v y)
  simpa only [y, countablePairAnnihilate_wedge] using h
end VortexGap.Fermion
