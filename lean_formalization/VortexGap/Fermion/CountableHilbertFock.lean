import VortexGap.Fermion.CountableHilbertCoordinates
import VortexGap.Fermion.CountablePairUnitaryCovariance
import VortexGap.Frame.CountableTwoFrameOverlap
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open VortexGap.Frame
open scoped InnerProduct ComplexOrder
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem hilbertCoordinates_car (e : H ≃ₗᵢ[ℂ] CountableOrbital) (u v : H) :
    countableAnnihilate (e u) * countableCreate (e v) +
      countableCreate (e v) * countableAnnihilate (e u) = (inner ℂ u v) • 1 := by
  rw [countableOrbital_car, e.inner_map_map]

theorem hilbertCoordinates_create_anticommute (e : H ≃ₗᵢ[ℂ] CountableOrbital) (u v : H) :
    countableCreate (e u) * countableCreate (e v) =
      -(countableCreate (e v) * countableCreate (e u)) :=
  countableCreate_anticommute _ _

theorem hilbertCoordinates_change_create (e f : H ≃ₗᵢ[ℂ] CountableOrbital)
    (u : H) (x : CountableSpace) :
    countableFockEquiv (e.symm.trans f)
      (countableCreate (e u) ((countableFockEquiv (e.symm.trans f)).symm x)) =
        countableCreate (f u) x := by
  simpa using countableFockEquiv_conjugate_create (e.symm.trans f) (e u) x

theorem hilbertCoordinates_change_annihilate (e f : H ≃ₗᵢ[ℂ] CountableOrbital)
    (u : H) (x : CountableSpace) :
    countableFockEquiv (e.symm.trans f)
      (countableAnnihilate (e u) ((countableFockEquiv (e.symm.trans f)).symm x)) =
        countableAnnihilate (f u) x := by
  simpa using countableFockEquiv_conjugate_annihilate (e.symm.trans f) (e u) x

theorem hilbertCoordinates_change_wedge (e f : H ≃ₗᵢ[ℂ] CountableOrbital) (u v : H) :
    countablePairMap (e.symm.trans f).toLinearIsometry (countableWedge (e u) (e v)) =
      countableWedge (f u) (f v) := by
  simpa using countableWedge_map (e.symm.trans f).toLinearIsometry (e u) (e v)

theorem hilbertCoordinates_change_pairLift (e f : H ≃ₗᵢ[ℂ] CountableOrbital)
    (N : ℕ) (Q : CountablePairSpace →L[ℂ] CountablePairSpace) :
    countablePairLift N (countablePairConjugate (e.symm.trans f).toLinearIsometry Q) =
      (countableFockSectorEquiv (e.symm.trans f) N : countableSector N →L[ℂ] countableSector N).comp
        ((countablePairLift N Q).comp
          (countableFockSectorEquiv (e.symm.trans f) N : countableSector N →L[ℂ] countableSector N).adjoint) :=
  countablePairLift_unitary_conjugation _ _ _

theorem hilbertCoordinates_overlap (e : H ≃ₗᵢ[ℂ] CountableOrbital)
    (U V : TwoSpace →ₗᵢ[ℂ] H) :
    countableTwoFrameOverlap (e.toLinearIsometry.comp U) (e.toLinearIsometry.comp V) =
      (U.toContinuousLinearMap.adjoint.comp V.toContinuousLinearMap).toLinearMap := by
  apply LinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  change inner ℂ y ((e.toLinearIsometry.comp U).toContinuousLinearMap.adjoint (e (V x))) =
    inner ℂ y (U.toContinuousLinearMap.adjoint (V x))
  rw [ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_right]
  exact e.inner_map_map (U y) (V x)

theorem hilbertCoordinates_filter_nonneg (e : H ≃ₗᵢ[ℂ] CountableOrbital)
    (M : H →L[ℂ] H) (hM : 0 ≤ M) : 0 ≤ e.conjStarAlgEquiv M := by
  apply ContinuousLinearMap.nonneg_iff_isPositive.mpr
  have h := (ContinuousLinearMap.nonneg_iff_isPositive.mp hM).conj_adjoint
    e.toLinearIsometry.toContinuousLinearMap
  change (((e : H →L[ℂ] CountableOrbital).comp M).comp
    (e : H →L[ℂ] CountableOrbital).adjoint).IsPositive at h
  rw [e.adjoint_eq_symm] at h
  exact h

theorem hilbertCoordinates_filter_norm (e : H ≃ₗᵢ[ℂ] CountableOrbital)
    (M : H →L[ℂ] H) : ‖e.conjStarAlgEquiv M‖ = ‖M‖ :=
  StarAlgEquiv.norm_map e.conjStarAlgEquiv M

theorem hilbertCoordinates_filter_delta (e : H ≃ₗᵢ[ℂ] CountableOrbital)
    (M : H →L[ℂ] H) : ‖1 - (e.conjStarAlgEquiv M)^2‖ = ‖1-M^2‖ := by
  rw [← map_pow, ← map_one e.conjStarAlgEquiv, ← map_sub]
  exact StarAlgEquiv.norm_map e.conjStarAlgEquiv _
end VortexGap.Fermion