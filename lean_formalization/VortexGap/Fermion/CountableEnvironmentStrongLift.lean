import VortexGap.Fermion.CountableReferenceLimits
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open Filter
open scoped BigOperators Topology

theorem countableEnvironmentAmplify_sum {ι : Type*} (s : Finset ι)
    (Q : ι → CountableSpace →L[ℂ] CountableSpace) :
    countableEnvironmentAmplify (∑ i ∈ s, Q i) = ∑ i ∈ s, countableEnvironmentAmplify (Q i) := by
  ext x AB
  rcases AB with ⟨A,B⟩
  simp only [countableEnvironmentAmplify_apply, sum_apply, lp.coeFn_sum, Finset.sum_apply]

theorem countableEnvironmentLift_truncate (N : ℕ)
    (Q : CountablePairSpace →L[ℂ] CountablePairSpace)
    (s : Finset CountablePairIndex) (x : countableSector N) :
    countableFockSplit (countablePairLift N
      (countablePairConjugate countableEnvOrbital (Q.comp (countablePairTruncate s))) x) =
    countableEnvironmentAmplify (countableReferenceUpTo N (Q.comp (countablePairTruncate s)))
      (countableFockSplit x) := by
  rw [countablePairTruncate_comp_rankOne]
  simp only [countablePairConjugate_sum, countablePairLift_sum, countableReferenceUpTo_sum,
    countableEnvironmentAmplify_sum, sum_apply, Submodule.coe_sum, map_sum]
  apply Finset.sum_congr rfl
  intro a ha
  exact countableEnvironmentLift_rankOne N (Q (lp.single 2 a 1)) (lp.single 2 a 1) x

/-- Identification of the actual environment-embedded Hamiltonian with the
reference sector direct sum and its spectator amplification, for arbitrary bounded Q. -/
theorem countableEnvironmentLift_identification (N : ℕ)
    (Q : CountablePairSpace →L[ℂ] CountablePairSpace) (x : countableSector N) :
    countableFockSplit (countablePairLift N (countablePairConjugate countableEnvOrbital Q) x) =
    countableEnvironmentAmplify (countableReferenceUpTo N Q) (countableFockSplit x) := by
  let A (s : Finset CountablePairIndex) := Q.comp (countablePairTruncate s)
  have hb (s : Finset CountablePairIndex) : ‖A s‖ ≤ ‖Q‖ :=
    countablePairTruncate_comp_bound Q s
  have ht (p : CountablePairSpace) : Tendsto (fun s => A s p) atTop (𝓝 (Q p)) :=
    countablePairTruncate_comp_tendsto Q p
  let W : countableSector N →L[ℂ] CountableSplitSpace :=
    countableFockSplit.toLinearIsometry.toContinuousLinearMap.comp (countableSector N).subtypeL
  have hl := W.continuous.continuousAt.tendsto.comp
    (countablePairLift_tendsto N (fun s => countablePairConjugate countableEnvOrbital (A s))
      (countablePairConjugate countableEnvOrbital Q) ‖Q‖ (norm_nonneg _)
      (fun s => (countablePairConjugate_norm_le countableEnvOrbital (A s)).trans (hb s))
      (countablePairConjugate_tendsto countableEnvOrbital A Q ht) x)
  have hr := countableEnvironmentReference_tendsto N A Q ‖Q‖ (norm_nonneg _) hb ht
    (countableFockSplit x)
  have heq : (fun s => W (countablePairLift N
      (countablePairConjugate countableEnvOrbital (A s)) x)) =
      (fun s => countableEnvironmentAmplify (countableReferenceUpTo N (A s)) (countableFockSplit x)) :=
    funext (fun s => countableEnvironmentLift_truncate N Q s x)
  change Tendsto (fun s => W (countablePairLift N
      (countablePairConjugate countableEnvOrbital (A s)) x)) atTop
      (𝓝 (W (countablePairLift N (countablePairConjugate countableEnvOrbital Q) x))) at hl
  rw [heq] at hl
  exact tendsto_nhds_unique hl hr
end VortexGap.Fermion
