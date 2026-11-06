import VortexGap.Fermion.CountableEnvironmentPair
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped InnerProduct

theorem countableEnvironmentLift_rankOne_inner (N : ℕ)
    (p q : CountablePairSpace) (x y : countableSector N) :
    inner ℂ y (countablePairLift N
      (countablePairConjugate countableEnvOrbital (InnerProductSpace.rankOne ℂ p q)) x) =
    inner ℂ (countableFockSplit y)
      (countableEnvironmentAmplify (countableReferenceUpTo N (InnerProductSpace.rankOne ℂ p q))
        (countableFockSplit x)) := by
  rw [countablePairConjugate_rankOne, countablePairLift_rankOne,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
  rw [← countableFockSplit.inner_map_map
    (countablePairAnnihilate N (countablePairMap countableEnvOrbital p) y)
    (countablePairAnnihilate N (countablePairMap countableEnvOrbital q) x)]
  rw [countableEnvironment_inner, countableEnvironment_inner]
  apply tsum_congr
  intro B
  rw [countableEnvironmentFiber_pairAnnihilate, countableEnvironmentFiber_pairAnnihilate,
    countableEnvironmentAmplify_fiber]
  let xf : countableSector (N-B.card) :=
    ⟨countableEnvironmentFiber (countableFockSplit x) B,
      countableEnvironmentFiber_sector (countableFockSplit_sector x.property) B⟩
  let yf : countableSector (N-B.card) :=
    ⟨countableEnvironmentFiber (countableFockSplit y) B,
      countableEnvironmentFiber_sector (countableFockSplit_sector y.property) B⟩
  rw [countableReferenceUpTo_apply_sector N (N-B.card) (Nat.sub_le _ _)
    (InnerProductSpace.rankOne ℂ p q) xf]
  change inner ℂ (countablePairAnnihilate (N-B.card) p yf)
    (countablePairAnnihilate (N-B.card) q xf) =
    inner ℂ yf (countablePairLift (N-B.card) (InnerProductSpace.rankOne ℂ p q) xf)
  rw [countablePairLift_rankOne, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right]

theorem countableEnvironmentLift_rankOne (N : ℕ)
    (p q : CountablePairSpace) (x : countableSector N) :
    countableFockSplit (countablePairLift N
      (countablePairConjugate countableEnvOrbital (InnerProductSpace.rankOne ℂ p q)) x) =
    countableEnvironmentAmplify (countableReferenceUpTo N (InnerProductSpace.rankOne ℂ p q))
      (countableFockSplit x) := by
  let z : countableSector N := ⟨countableFockJoin
    (countableEnvironmentAmplify (countableReferenceUpTo N (InnerProductSpace.rankOne ℂ p q))
      (countableFockSplit x)),
    countableFockJoin_sector (countableEnvironmentReference_preserves_total N _
      (countableFockSplit_sector x.property))⟩
  have h : countablePairLift N
      (countablePairConjugate countableEnvOrbital (InnerProductSpace.rankOne ℂ p q)) x = z := by
    apply ext_inner_left ℂ
    intro y
    rw [countableEnvironmentLift_rankOne_inner]
    change _ = inner ℂ (y : CountableSpace) (z : CountableSpace)
    rw [← countableFockSplit.inner_map_map (y : CountableSpace) (z : CountableSpace)]
    change _ = inner ℂ (countableFockSplit y)
      (countableFockJoin.symm (countableFockJoin _))
    rw [countableFockJoin.symm_apply_apply]
  have hh := congrArg (fun v : countableSector N => countableFockSplit v) h
  change _ = countableFockJoin.symm (countableFockJoin _) at hh
  simpa only [countableFockJoin.symm_apply_apply] using hh
end VortexGap.Fermion
