import VortexGap.Fermion.CountablePairStrongCovariance
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion

theorem countablePairLift_unitary_apply
    (U : CountableOrbital ≃ₗᵢ[ℂ] CountableOrbital) (N : ℕ)
    (Q : CountablePairSpace →L[ℂ] CountablePairSpace) (x : countableSector N) :
    countablePairLift N (countablePairConjugate U.toLinearIsometry Q)
      (countableFockSectorEquiv U N x) =
    countableFockSectorEquiv U N (countablePairLift N Q x) := by
  let e := countableFockSectorEquiv U N
  have h := congrArg (fun T : countableSector N →L[ℂ] countableSector N => T x)
    (countablePairLift_compression U.toLinearIsometry N Q)
  change (e : countableSector N →L[ℂ] countableSector N).adjoint
    (countablePairLift N (countablePairConjugate U.toLinearIsometry Q) (e x)) =
      countablePairLift N Q x at h
  rw [e.adjoint_eq_symm] at h
  have hh := congrArg e h
  simpa only [LinearIsometryEquiv.coe_coe'', LinearIsometryEquiv.apply_symm_apply] using hh

/-- Full fixed-sector conjugation, rather than merely compression, follows
from the concrete surjective Fock implementation of a one-particle unitary. -/
theorem countablePairLift_unitary_conjugation
    (U : CountableOrbital ≃ₗᵢ[ℂ] CountableOrbital) (N : ℕ)
    (Q : CountablePairSpace →L[ℂ] CountablePairSpace) :
    countablePairLift N (countablePairConjugate U.toLinearIsometry Q) =
      (countableFockSectorEquiv U N : countableSector N →L[ℂ] countableSector N).comp
        ((countablePairLift N Q).comp
          (countableFockSectorEquiv U N : countableSector N →L[ℂ] countableSector N).adjoint) := by
  apply ContinuousLinearMap.ext
  intro x
  rw [(countableFockSectorEquiv U N).adjoint_eq_symm]
  simpa only [LinearIsometryEquiv.coe_coe'', LinearIsometryEquiv.apply_symm_apply,
    ContinuousLinearMap.comp_apply] using
    countablePairLift_unitary_apply U N Q ((countableFockSectorEquiv U N).symm x)
end VortexGap.Fermion
