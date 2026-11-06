import VortexGap.Fermion.CountablePairConjugation
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open Filter
open scoped InnerProduct BigOperators Topology

theorem countablePairLift_truncate_compression
    (J : CountableOrbital →ₗᵢ[ℂ] CountableOrbital) (N : ℕ)
    (Q : CountablePairSpace →L[ℂ] CountablePairSpace) (s : Finset CountablePairIndex) :
    (countableFockSector J N).toContinuousLinearMap.adjoint.comp
      ((countablePairLift N (countablePairConjugate J
        (Q.comp (countablePairTruncate s)))).comp
        (countableFockSector J N).toContinuousLinearMap) =
    countablePairLift N (Q.comp (countablePairTruncate s)) := by
  rw [countablePairTruncate_comp_rankOne, countablePairConjugate_sum,
    countablePairLift_sum, countablePairLift_sum]
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply, sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [countablePairConjugate_rankOne]
  exact congrArg (fun T : countableSector N →L[ℂ] countableSector N => T x)
    (countablePairLift_rankOne_compression J N (Q (lp.single 2 a 1)) (lp.single 2 a 1))

/-- Compression through the actual completed Fock isometry, for every bounded
pair operator. Finite-rank approximants are used only for strong limits. -/
theorem countablePairLift_compression
    (J : CountableOrbital →ₗᵢ[ℂ] CountableOrbital) (N : ℕ)
    (Q : CountablePairSpace →L[ℂ] CountablePairSpace) :
    (countableFockSector J N).toContinuousLinearMap.adjoint.comp
      ((countablePairLift N (countablePairConjugate J Q)).comp
        (countableFockSector J N).toContinuousLinearMap) =
    countablePairLift N Q := by
  let V := (countableFockSector J N).toContinuousLinearMap
  let A (s : Finset CountablePairIndex) := Q.comp (countablePairTruncate s)
  have hf (s : Finset CountablePairIndex) :
      V.adjoint.comp ((countablePairLift N (countablePairConjugate J (A s))).comp V) =
        countablePairLift N (A s) := countablePairLift_truncate_compression J N Q s
  have hb (s : Finset CountablePairIndex) : ‖A s‖ ≤ ‖Q‖ :=
    countablePairTruncate_comp_bound Q s
  have ht (p : CountablePairSpace) : Tendsto (fun s => A s p) atTop (𝓝 (Q p)) :=
    countablePairTruncate_comp_tendsto Q p
  apply ContinuousLinearMap.ext
  intro x
  have hr := countablePairLift_tendsto N A Q ‖Q‖ (norm_nonneg _) hb ht x
  have hl := V.adjoint.continuous.continuousAt.tendsto.comp
    (countablePairLift_tendsto N (fun s => countablePairConjugate J (A s))
      (countablePairConjugate J Q) ‖Q‖ (norm_nonneg _)
      (fun s => (countablePairConjugate_norm_le J (A s)).trans (hb s))
      (countablePairConjugate_tendsto J A Q ht) (V x))
  have heq : (fun s => V.adjoint (countablePairLift N
      (countablePairConjugate J (A s)) (V x))) =
      (fun s => countablePairLift N (A s) x) :=
    funext (fun s => congrArg (fun T : countableSector N →L[ℂ] countableSector N => T x) (hf s))
  change Tendsto (fun s => V.adjoint (countablePairLift N
      (countablePairConjugate J (A s)) (V x))) atTop
      (𝓝 (V.adjoint (countablePairLift N (countablePairConjugate J Q) (V x)))) at hl
  rw [heq] at hl
  exact tendsto_nhds_unique hl hr
end VortexGap.Fermion
