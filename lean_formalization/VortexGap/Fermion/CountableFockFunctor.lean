import VortexGap.Fermion.CountableFockCovariance

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion

theorem countableFockIsometry_comp
    (K J : CountableOrbital →ₗᵢ[ℂ] CountableOrbital) :
    countableFockIsometry (K.comp J) = (countableFockIsometry K).comp (countableFockIsometry J) := by
  apply LinearIsometry.toContinuousLinearMap_injective
  apply countableSpace_clm_ext
  intro A
  change countableFockIsometry (K.comp J) (countableKet A) =
    countableFockIsometry K (countableFockIsometry J (countableKet A))
  rw [countableFockIsometry_ket, countableFockIsometry_ket,
    countableFockIsometry_occupationImage]
  rfl

theorem countableFockIsometry_comp_apply
    (K J : CountableOrbital →ₗᵢ[ℂ] CountableOrbital) (x : CountableSpace) :
    countableFockIsometry (K.comp J) x = countableFockIsometry K (countableFockIsometry J x) :=
  congrArg (fun T : CountableSpace →ₗᵢ[ℂ] CountableSpace => T x) (countableFockIsometry_comp K J)

theorem countableFockSector_comp
    (K J : CountableOrbital →ₗᵢ[ℂ] CountableOrbital) (N : ℕ) :
    countableFockSector (K.comp J) N = (countableFockSector K N).comp (countableFockSector J N) := by
  apply LinearIsometry.ext
  intro x
  apply Subtype.ext
  exact countableFockIsometry_comp_apply K J x

theorem countableFockSector_id (N : ℕ) :
    countableFockSector (LinearIsometry.id : CountableOrbital →ₗᵢ[ℂ] CountableOrbital) N =
      (LinearIsometry.id : countableSector N →ₗᵢ[ℂ] countableSector N) := by
  apply LinearIsometry.ext
  intro x
  apply Subtype.ext
  change countableFockIsometry LinearIsometry.id (x : CountableSpace) = x
  simp only [countableFockIsometry_id, LinearIsometry.id_apply]

theorem countableFockIsometry_left_inverse
    (U : CountableOrbital ≃ₗᵢ[ℂ] CountableOrbital) (x : CountableSpace) :
    countableFockIsometry U.symm.toLinearIsometry
      (countableFockIsometry U.toLinearIsometry x) = x := by
  have hU : U.symm.toLinearIsometry.comp U.toLinearIsometry = LinearIsometry.id := by
    apply LinearIsometry.ext
    intro v
    exact U.symm_apply_apply v
  rw [← countableFockIsometry_comp_apply, hU, countableFockIsometry_id]
  rfl

theorem countableFockIsometry_right_inverse
    (U : CountableOrbital ≃ₗᵢ[ℂ] CountableOrbital) (x : CountableSpace) :
    countableFockIsometry U.toLinearIsometry
      (countableFockIsometry U.symm.toLinearIsometry x) = x := by
  have hU : U.toLinearIsometry.comp U.symm.toLinearIsometry = LinearIsometry.id := by
    apply LinearIsometry.ext
    intro v
    exact U.apply_symm_apply v
  rw [← countableFockIsometry_comp_apply, hU, countableFockIsometry_id]
  rfl

/-- A one-particle unitary gives an actual complete-Fock unitary with the explicit inverse. -/
def countableFockEquiv (U : CountableOrbital ≃ₗᵢ[ℂ] CountableOrbital) :
    CountableSpace ≃ₗᵢ[ℂ] CountableSpace where
  toFun := countableFockIsometry U.toLinearIsometry
  map_add' := map_add (countableFockIsometry U.toLinearIsometry)
  map_smul' := map_smul (countableFockIsometry U.toLinearIsometry)
  norm_map' := (countableFockIsometry U.toLinearIsometry).norm_map
  invFun := countableFockIsometry U.symm.toLinearIsometry
  left_inv := countableFockIsometry_left_inverse U
  right_inv := countableFockIsometry_right_inverse U

theorem countableFockEquiv_apply (U : CountableOrbital ≃ₗᵢ[ℂ] CountableOrbital)
    (x : CountableSpace) : countableFockEquiv U x = countableFockIsometry U.toLinearIsometry x := rfl

theorem countableFockEquiv_symm_apply (U : CountableOrbital ≃ₗᵢ[ℂ] CountableOrbital)
    (x : CountableSpace) :
    (countableFockEquiv U).symm x = countableFockIsometry U.symm.toLinearIsometry x := rfl

theorem countableFockEquiv_sector_iff (U : CountableOrbital ≃ₗᵢ[ℂ] CountableOrbital)
    (N : ℕ) (x : CountableSpace) :
    countableFockEquiv U x ∈ countableSector N ↔ x ∈ countableSector N := by
  constructor
  · intro hx
    have h := countableFockIsometry_sector U.symm.toLinearIsometry hx
    simpa only [countableFockEquiv_apply, countableFockIsometry_left_inverse] using h
  · exact countableFockIsometry_sector U.toLinearIsometry

def countableFockSectorEquiv (U : CountableOrbital ≃ₗᵢ[ℂ] CountableOrbital) (N : ℕ) :
    countableSector N ≃ₗᵢ[ℂ] countableSector N where
  toFun := countableFockSector U.toLinearIsometry N
  map_add' := map_add (countableFockSector U.toLinearIsometry N)
  map_smul' := map_smul (countableFockSector U.toLinearIsometry N)
  norm_map' := (countableFockSector U.toLinearIsometry N).norm_map
  invFun := countableFockSector U.symm.toLinearIsometry N
  left_inv x := Subtype.ext (countableFockIsometry_left_inverse U x)
  right_inv x := Subtype.ext (countableFockIsometry_right_inverse U x)

theorem countableFockSectorEquiv_apply (U : CountableOrbital ≃ₗᵢ[ℂ] CountableOrbital)
    (N : ℕ) (x : countableSector N) :
    (countableFockSectorEquiv U N x : CountableSpace) = countableFockEquiv U x := rfl

theorem countableFockSectorEquiv_symm_apply (U : CountableOrbital ≃ₗᵢ[ℂ] CountableOrbital)
    (N : ℕ) (x : countableSector N) :
    ((countableFockSectorEquiv U N).symm x : CountableSpace) = (countableFockEquiv U).symm x := rfl

theorem countableFockEquiv_conjugate_create (U : CountableOrbital ≃ₗᵢ[ℂ] CountableOrbital)
    (v : CountableOrbital) (x : CountableSpace) :
    countableFockEquiv U (countableCreate v ((countableFockEquiv U).symm x)) =
      countableCreate (U v) x := by
  rw [countableFockEquiv_apply, countableFockIsometry_create]
  change countableCreate (U v) (countableFockEquiv U ((countableFockEquiv U).symm x)) = _
  rw [(countableFockEquiv U).apply_symm_apply]

theorem countableFockEquiv_conjugate_annihilate (U : CountableOrbital ≃ₗᵢ[ℂ] CountableOrbital)
    (v : CountableOrbital) (x : CountableSpace) :
    countableFockEquiv U (countableAnnihilate v ((countableFockEquiv U).symm x)) =
      countableAnnihilate (U v) x := by
  rw [countableFockEquiv_apply, countableFockIsometry_annihilate]
  change countableAnnihilate (U v) (countableFockEquiv U ((countableFockEquiv U).symm x)) = _
  rw [(countableFockEquiv U).apply_symm_apply]

end VortexGap.Fermion
