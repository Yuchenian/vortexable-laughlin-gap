import VortexGap.Fermion.CountableWedgeCreation
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped ComplexOrder

/-- Concrete one-column Hamiltonian output on environment vacuum.
The two noise amplitudes are explicit creation maps applied to the filtered pair field. -/
theorem countableLoss_rankOne_output
    (M : CountableOrbital →L[ℂ] CountableOrbital) (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1)
    {N : ℕ} (u v : CountableOrbital) (x : countableSector (N+2)) :
    (countablePairLift (N+2)
      (countablePairConjugate (countableLossEmbedding M hM hc)
        (InnerProductSpace.rankOne ℂ (countableWedge u v) (countableWedge u v)))
      (countableFockSector countableSysOrbital (N+2) x) : CountableSpace) =
    countableFockIsometry countableSysOrbital
      (countablePairLift (N+2)
        (InnerProductSpace.rankOne ℂ (countableWedge (M u) (M v)) (countableWedge (M u) (M v))) x) +
    countableLossCreationOne M u v
      (countablePairAnnihilate (N+2) (countableWedge (M u) (M v)) x) +
    countableLossCreationTwo M u v
      (countablePairAnnihilate (N+2) (countableWedge (M u) (M v)) x) := by
  simp only [countablePairConjugate_rankOne, countableWedge_map,
    countablePairLift_wedge_rankOne, countableFockSector_apply, countablePairAnnihilate_wedge]
  rw [countableLoss_double_annihilate_system, countableLoss_creation_output]
  rfl

/-- Orthogonal vacuum output identity for the actual rank-one pair Hamiltonian,
not an assumed variance relation. -/
theorem countableLoss_rankOne_output_norm_sq
    (M : CountableOrbital →L[ℂ] CountableOrbital) (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1)
    {N : ℕ} (u v : CountableOrbital) (x : countableSector (N+2)) :
    ‖(countablePairLift (N+2)
      (countablePairConjugate (countableLossEmbedding M hM hc)
        (InnerProductSpace.rankOne ℂ (countableWedge u v) (countableWedge u v)))
      (countableFockSector countableSysOrbital (N+2) x) : CountableSpace)‖^2 =
    ‖(countablePairLift (N+2)
      (InnerProductSpace.rankOne ℂ (countableWedge (M u) (M v)) (countableWedge (M u) (M v))) x :
      CountableSpace)‖^2 +
    ‖countableLossCreationOne M u v
      (countablePairAnnihilate (N+2) (countableWedge (M u) (M v)) x)‖^2 +
    ‖countableLossCreationTwo M u v
      (countablePairAnnihilate (N+2) (countableWedge (M u) (M v)) x)‖^2 := by
  simp only [countablePairConjugate_rankOne, countableWedge_map,
    countablePairLift_wedge_rankOne, countableFockSector_apply, countablePairAnnihilate_wedge]
  rw [countableLoss_double_annihilate_system, countableLoss_creation_norm_sq]
  simp only [countableLossCreationZero, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, (countableFockIsometry countableSysOrbital).norm_map]
end VortexGap.Fermion
