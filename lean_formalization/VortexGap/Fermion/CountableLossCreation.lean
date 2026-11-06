import VortexGap.Fermion.CountableVacuumLoss
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped ComplexOrder

def countableLossCreationZero (M : CountableOrbital →L[ℂ] CountableOrbital)
    (u v : CountableOrbital) : CountableSpace →L[ℂ] CountableSpace :=
  (countableFockIsometry countableSysOrbital).toContinuousLinearMap.comp
    ((countableCreate (M u)).comp (countableCreate (M v)))

def countableLossCreationOne (M : CountableOrbital →L[ℂ] CountableOrbital)
    (u v : CountableOrbital) : CountableSpace →L[ℂ] CountableSpace :=
  (countableCreate (countableEnvOrbital (lossDefect M u))).comp
    ((countableFockIsometry countableSysOrbital).toContinuousLinearMap.comp (countableCreate (M v))) -
  (countableCreate (countableEnvOrbital (lossDefect M v))).comp
    ((countableFockIsometry countableSysOrbital).toContinuousLinearMap.comp (countableCreate (M u)))

def countableLossCreationTwo (M : CountableOrbital →L[ℂ] CountableOrbital)
    (u v : CountableOrbital) : CountableSpace →L[ℂ] CountableSpace :=
  (countableCreate (countableEnvOrbital (lossDefect M u))).comp
    ((countableCreate (countableEnvOrbital (lossDefect M v))).comp
      (countableFockIsometry countableSysOrbital).toContinuousLinearMap)

/-- Exact ordered two-creation output; the mixed sign is derived from CAR. -/
theorem countableLoss_creation_output
    (M : CountableOrbital →L[ℂ] CountableOrbital) (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1)
    (u v : CountableOrbital) (x : CountableSpace) :
    countableCreate (countableLossEmbedding M hM hc u)
      (countableCreate (countableLossEmbedding M hM hc v)
        (countableFockIsometry countableSysOrbital x)) =
    countableLossCreationZero M u v x + countableLossCreationOne M u v x +
      countableLossCreationTwo M u v x := by
  have hcross := congrArg (fun T : CountableSpace →L[ℂ] CountableSpace =>
      T (countableFockIsometry countableSysOrbital x))
    (countableCreate_anticommute (countableSysOrbital (M u))
      (countableEnvOrbital (lossDefect M v)))
  change countableCreate (countableSysOrbital (M u))
      (countableCreate (countableEnvOrbital (lossDefect M v))
        (countableFockIsometry countableSysOrbital x)) =
    -countableCreate (countableEnvOrbital (lossDefect M v))
      (countableCreate (countableSysOrbital (M u))
        (countableFockIsometry countableSysOrbital x)) at hcross
  simp only [countableLossCreationZero, countableLossCreationOne, countableLossCreationTwo,
    ContinuousLinearMap.comp_apply, sub_apply, LinearIsometry.coe_toContinuousLinearMap,
    countableFockIsometry_create, countableLossEmbedding_apply, map_add, add_apply]
  rw [hcross]
  abel
end VortexGap.Fermion
