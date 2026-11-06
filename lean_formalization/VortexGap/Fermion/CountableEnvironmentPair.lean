import VortexGap.Fermion.CountableEnvironmentReference
import VortexGap.Fermion.CountableLossPairLift
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion

theorem countableEnvironmentFiber_annihilate (v : CountableOrbital)
    (x : CountableSpace) (B : Finset ℕ) :
    countableEnvironmentFiber
      (countableFockSplit (countableAnnihilate (countableEnvOrbital v) x)) B =
    countableAnnihilate v (countableEnvironmentFiber (countableFockSplit x) B) := by
  ext A
  have h := countableSplit_annihilate_env_orbital_coordinate v (countableFockSplit x) A B
  simpa only [countableSplitConjugate_apply, countableFockSplit,
    countableFockJoin.apply_symm_apply, countableEnvironmentFiber_apply] using h

/-- Exact spectator fiber action of the actual environment pair field,
including all nondecomposable square-summable pair waves. -/
theorem countableEnvironmentFiber_pairAnnihilate {N : ℕ}
    (p : CountablePairSpace) (x : countableSector N) (B : Finset ℕ) :
    countableEnvironmentFiber
      (countableFockSplit (countablePairAnnihilate N (countablePairMap countableEnvOrbital p) x)) B =
    countablePairAnnihilate (N-B.card) p
      ⟨countableEnvironmentFiber (countableFockSplit x) B,
        countableEnvironmentFiber_sector (countableFockSplit_sector x.property) B⟩ := by
  let y : countableSector (N-B.card) :=
    ⟨countableEnvironmentFiber (countableFockSplit x) B,
      countableEnvironmentFiber_sector (countableFockSplit_sector x.property) B⟩
  ext A
  let L : CountablePairSpace →L⋆[ℂ] ℂ :=
    (lp.evalCLM ℂ _ 2 (A,B)).comp
      (countableFockSplit.toLinearIsometry.toContinuousLinearMap.comp
        ((ContinuousLinearMap.apply ℂ CountableSpace x).comp
          ((countablePairAnnihilateWave N).comp (countablePairMap countableEnvOrbital))))
  let R : CountablePairSpace →L⋆[ℂ] ℂ :=
    (lp.evalCLM ℂ _ 2 A).comp
      ((ContinuousLinearMap.apply ℂ CountableSpace y).comp (countablePairAnnihilateWave (N-B.card)))
  have h : L = R := by
    apply countablePair_antilinear_ext
    intro a
    change countableEnvironmentFiber
      (countableFockSplit (countablePairAnnihilate N
        (countablePairMap countableEnvOrbital (lp.single 2 a 1)) x)) B A =
      countablePairAnnihilate (N-B.card) (lp.single 2 a 1) y A
    rw [← countableWedge_basis a, countableWedge_map,
      countablePairAnnihilate_wedge, countablePairAnnihilate_wedge,
      countableEnvironmentFiber_annihilate, countableEnvironmentFiber_annihilate]
  exact congrArg (fun T : CountablePairSpace →L⋆[ℂ] ℂ => T p) h
end VortexGap.Fermion
