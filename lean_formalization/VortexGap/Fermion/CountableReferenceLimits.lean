import VortexGap.Fermion.CountableEnvironmentLift
import VortexGap.Operator.L2AmplificationLimits
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open Filter
open scoped BigOperators Topology

theorem countableSectorExtend_norm_le (N : ℕ)
    (T : countableSector N →L[ℂ] countableSector N) :
    ‖countableSectorExtend N T‖ ≤ ‖T‖ := by
  have h := (countableSector N).norm_subtypeL_le
  have ha : ‖(countableSector N).subtypeL.adjoint‖ ≤ 1 := by
    rwa [ContinuousLinearMap.adjoint.norm_map]
  unfold countableSectorExtend
  calc
    _ ≤ ‖(countableSector N).subtypeL‖ * ‖T.comp (countableSector N).subtypeL.adjoint‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * (‖T‖ * 1) := mul_le_mul h
      ((ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left ha (norm_nonneg T)))
      (ContinuousLinearMap.opNorm_nonneg _) (by norm_num)
    _ = ‖T‖ := by ring

theorem countableReferenceUpTo_norm_le (N : ℕ)
    (Q : CountablePairSpace →L[ℂ] CountablePairSpace) :
    ‖countableReferenceUpTo N Q‖ ≤ (∑ k ∈ Finset.range (N+1), (k.choose 2 : ℝ)) * ‖Q‖ := by
  unfold countableReferenceUpTo
  calc
    _ ≤ ∑ k ∈ Finset.range (N+1), ‖countableSectorExtend k (countablePairLift k Q)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range (N+1), (k.choose 2 : ℝ) * ‖Q‖ :=
      Finset.sum_le_sum (fun k _ =>
        (countableSectorExtend_norm_le k _).trans (countablePairLift_opNorm_le k Q))
    _ = _ := (Finset.sum_mul _ _ _).symm

theorem countableReferenceUpTo_sum (N : ℕ) {ι : Type*} (s : Finset ι)
    (Q : ι → CountablePairSpace →L[ℂ] CountablePairSpace) :
    countableReferenceUpTo N (∑ i ∈ s, Q i) = ∑ i ∈ s, countableReferenceUpTo N (Q i) := by
  ext x
  simp only [countableReferenceUpTo, countablePairLift_sum, countableSectorExtend,
    ContinuousLinearMap.comp_apply, sum_apply, map_sum]
  rw [Finset.sum_comm]

theorem countableReferenceUpTo_tendsto (N : ℕ) {ι : Type*} {l : Filter ι}
    (Q : ι → CountablePairSpace →L[ℂ] CountablePairSpace)
    (R : CountablePairSpace →L[ℂ] CountablePairSpace)
    (K : ℝ) (hK : 0 ≤ K) (hb : ∀ i, ‖Q i‖ ≤ K)
    (ht : ∀ p, Tendsto (fun i => Q i p) l (𝓝 (R p))) (x : CountableSpace) :
    Tendsto (fun i => countableReferenceUpTo N (Q i) x) l (𝓝 (countableReferenceUpTo N R x)) := by
  simp only [countableReferenceUpTo, sum_apply]
  apply tendsto_finsetSum
  intro k hk
  exact (countableSector k).subtypeL.continuous.continuousAt.tendsto.comp
    (countablePairLift_tendsto k Q R K hK hb ht ((countableSector k).subtypeL.adjoint x))

theorem countableEnvironmentAmplify_tendsto {ι : Type*} {l : Filter ι}
    (Q : ι → CountableSpace →L[ℂ] CountableSpace)
    (R : CountableSpace →L[ℂ] CountableSpace)
    (K : ℝ) (hK : 0 ≤ K) (hb : ∀ i, ‖Q i‖ ≤ K)
    (ht : ∀ x, Tendsto (fun i => Q i x) l (𝓝 (R x))) (x : CountableSplitSpace) :
    Tendsto (fun i => countableEnvironmentAmplify (Q i) x) l
      (𝓝 (countableEnvironmentAmplify R x)) :=
  countableSplitExchange.continuous.continuousAt.tendsto.comp
    (l2Amplify_tendsto (Finset ℕ) Q R K hK hb ht (countableSplitExchange x))

theorem countableEnvironmentReference_tendsto (N : ℕ) {ι : Type*} {l : Filter ι}
    (Q : ι → CountablePairSpace →L[ℂ] CountablePairSpace)
    (R : CountablePairSpace →L[ℂ] CountablePairSpace)
    (K : ℝ) (hK : 0 ≤ K) (hb : ∀ i, ‖Q i‖ ≤ K)
    (ht : ∀ p, Tendsto (fun i => Q i p) l (𝓝 (R p))) (x : CountableSplitSpace) :
    Tendsto (fun i => countableEnvironmentAmplify (countableReferenceUpTo N (Q i)) x) l
      (𝓝 (countableEnvironmentAmplify (countableReferenceUpTo N R) x)) := by
  let C : ℝ := ∑ k ∈ Finset.range (N+1), (k.choose 2 : ℝ)
  have hC : 0 ≤ C := Finset.sum_nonneg (fun k _ => Nat.cast_nonneg _)
  exact countableEnvironmentAmplify_tendsto _ _ (C*K) (mul_nonneg hC hK)
    (fun i => (countableReferenceUpTo_norm_le N (Q i)).trans
      (mul_le_mul_of_nonneg_left (hb i) hC))
    (countableReferenceUpTo_tendsto N Q R K hK hb ht) x
end VortexGap.Fermion
