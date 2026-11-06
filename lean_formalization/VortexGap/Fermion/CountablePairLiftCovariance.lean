import VortexGap.Fermion.CountablePairCovariance
import VortexGap.Fermion.CountablePairLift
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped InnerProduct

/-- A rank-one pair interaction compresses correctly through an arbitrary
one-particle isometry on every complete fixed-N sector. -/
theorem countablePairLift_rankOne_compression
    (J : CountableOrbital →ₗᵢ[ℂ] CountableOrbital) (N : ℕ)
    (p q : CountablePairSpace) :
    (countableFockSector J N).toContinuousLinearMap.adjoint.comp
      ((countablePairLift N (InnerProductSpace.rankOne ℂ
        (countablePairMap J p) (countablePairMap J q))).comp
        (countableFockSector J N).toContinuousLinearMap) =
    countablePairLift N (InnerProductSpace.rankOne ℂ p q) := by
  apply ContinuousLinearMap.ext
  intro y
  apply ext_inner_left ℂ
  intro x
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    countablePairLift_rankOne]
  change inner ℂ
    (countablePairAnnihilate N (countablePairMap J p)
      ⟨countableFockIsometry J x, countableFockIsometry_sector J x.property⟩)
    (countablePairAnnihilate N (countablePairMap J q)
      ⟨countableFockIsometry J y, countableFockIsometry_sector J y.property⟩) =
    inner ℂ (countablePairAnnihilate N p x) (countablePairAnnihilate N q y)
  rw [countablePairAnnihilate_covariance, countablePairAnnihilate_covariance,
    (countableFockIsometry J).inner_map_map]
end VortexGap.Fermion
