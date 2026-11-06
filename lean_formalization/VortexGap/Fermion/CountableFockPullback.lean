import VortexGap.Fermion.CountableFockCovariance

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped InnerProduct

/-- The target orbital may lie outside the embedded one-particle range. -/
theorem countableFock_annihilate_pullback_word
    (J : CountableOrbital →ₗᵢ[ℂ] CountableOrbital) (w : CountableOrbital) (js : List ℕ) :
    countableAnnihilate w (countableFockIsometry J (countableWord orbitalKet js)) =
      countableFockIsometry J
        (countableAnnihilate (J.toContinuousLinearMap.adjoint w) (countableWord orbitalKet js)) := by
  induction js with
  | nil =>
      simp only [countableWord_nil, countableFockIsometry_vacuum, countableAnnihilate_vacuum, map_zero]
  | cons j js ih =>
      rw [countableWord_cons, countableFockIsometry_create, countableAnnihilate_create,
        countableAnnihilate_create, map_sub, map_smul, countableFockIsometry_create, ih]
      rw [ContinuousLinearMap.adjoint_inner_left]
      rfl

theorem countableFock_annihilate_pullback_map
    (J : CountableOrbital →ₗᵢ[ℂ] CountableOrbital) (w : CountableOrbital) :
    (countableAnnihilate w).comp (countableFockIsometry J).toContinuousLinearMap =
      (countableFockIsometry J).toContinuousLinearMap.comp
        (countableAnnihilate (J.toContinuousLinearMap.adjoint w)) := by
  apply countableSpace_clm_ext
  intro A
  change countableAnnihilate w (countableFockIsometry J (countableKet A)) =
    countableFockIsometry J (countableAnnihilate (J.toContinuousLinearMap.adjoint w) (countableKet A))
  rw [← countableOccupationImage_orbitalKet A]
  exact countableFock_annihilate_pullback_word J w (A.sort (· ≤ ·))

theorem countableFock_annihilate_pullback
    (J : CountableOrbital →ₗᵢ[ℂ] CountableOrbital) (w : CountableOrbital) (x : CountableSpace) :
    countableAnnihilate w (countableFockIsometry J x) =
      countableFockIsometry J (countableAnnihilate (J.toContinuousLinearMap.adjoint w) x) :=
  congrArg (fun T : CountableSpace →L[ℂ] CountableSpace => T x)
    (countableFock_annihilate_pullback_map J w)

theorem countableFock_compress_annihilate
    (J : CountableOrbital →ₗᵢ[ℂ] CountableOrbital) (w : CountableOrbital) :
    (countableFockIsometry J).toContinuousLinearMap.adjoint.comp
      ((countableAnnihilate w).comp (countableFockIsometry J).toContinuousLinearMap) =
        countableAnnihilate (J.toContinuousLinearMap.adjoint w) := by
  rw [countableFock_annihilate_pullback_map]
  change ((countableFockIsometry J).toContinuousLinearMap.adjoint.comp
    (countableFockIsometry J).toContinuousLinearMap).comp
      (countableAnnihilate (J.toContinuousLinearMap.adjoint w)) = _
  rw [countableFockIsometry_adjoint_self]
  rfl

theorem countableFock_compress_create
    (J : CountableOrbital →ₗᵢ[ℂ] CountableOrbital) (w : CountableOrbital) :
    (countableFockIsometry J).toContinuousLinearMap.adjoint.comp
      ((countableCreate w).comp (countableFockIsometry J).toContinuousLinearMap) =
        countableCreate (J.toContinuousLinearMap.adjoint w) := by
  have h := congrArg (fun T : CountableSpace →L[ℂ] CountableSpace => T.adjoint)
    (countableFock_compress_annihilate J w)
  simpa only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
    countableAnnihilate_adjoint, ContinuousLinearMap.comp_assoc] using h

theorem countableFock_annihilate_orthogonal
    (J : CountableOrbital →ₗᵢ[ℂ] CountableOrbital) (w : CountableOrbital)
    (hw : J.toContinuousLinearMap.adjoint w = 0) (x : CountableSpace) :
    countableAnnihilate w (countableFockIsometry J x) = 0 := by
  rw [countableFock_annihilate_pullback, hw]
  simp only [countableAnnihilate, map_zero, zero_apply]

end VortexGap.Fermion
