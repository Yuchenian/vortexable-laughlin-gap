import VortexGap.Reference.PairCompression
import VortexGap.Reference.DegreeSupport
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped BigOperators InnerProduct

def PairDegreeAtMost (L : ℕ) (q : CountablePairSpace) : Prop :=
  ∀ a : CountablePairIndex, L < a.val.1+a.val.2 → q a = 0

theorem finitePairEmbedding_adjoint_coefficient (n : ℕ) (q : CountablePairSpace)
    (a : PairIndex n) :
    (finitePairEmbedding n).toContinuousLinearMap.adjoint q a = q (pairIndexNat a) := by
  have h := ContinuousLinearMap.adjoint_inner_right
    (finitePairEmbedding n).toContinuousLinearMap (pairBasis a) q
  simp only [LinearIsometry.coe_toContinuousLinearMap] at h
  rw [finitePairEmbedding_basis] at h
  simpa [pairBasis, EuclideanSpace.inner_single_left, lp.inner_single_left] using h

theorem pairDegree_exact_finite (L : ℕ) (q : CountablePairSpace)
    (hq : PairDegreeAtMost L q) :
    finitePairEmbedding (L+1) ((finitePairEmbedding (L+1)).toContinuousLinearMap.adjoint q) = q := by
  ext a
  by_cases hj : a.val.2 < L+1
  · have hi : a.val.1 < L+1 := lt_trans a.property hj
    let b : PairIndex (L+1) := ⟨(⟨a.val.1,hi⟩,⟨a.val.2,hj⟩),a.property⟩
    have hb : pairIndexNat b = a := rfl
    rw [← hb, finitePairEmbedding_coefficient, finitePairEmbedding_adjoint_coefficient]
  · rw [finitePairEmbedding_outside _ a (by omega)]
    exact (hq a (by omega)).symm

theorem planeBlock_inner_zero_of_degree (L n : ℕ) (q : CountablePairSpace)
    (hq : PairDegreeAtMost L q) (hn : L < n) : inner ℂ (planeBlockVector n) q = 0 := by
  rw [planeBlockVector, sum_inner]
  apply Finset.sum_eq_zero
  intro i hi
  have hz := hq (planeBlockIndex n i) (by rw [planeBlockIndex_total]; exact hn)
  rw [inner_smul_left]
  simp [lp.inner_single_left, hz]

theorem finitePairEmbedding_planeFiniteBlock (L p : ℕ) (hp : p+1 ≤ L) :
    finitePairEmbedding (L+1) (planeFiniteBlock L p) = planeBlockVector (p+1) := by
  have hd : PairDegreeAtMost L (planeBlockVector (p+1)) := by
    intro a ha
    apply planeBlockVector_off_block
    omega
  have he := pairDegree_exact_finite L (planeBlockVector (p+1)) hd
  rw [finitePairEmbedding_adjoint_planeBlock] at he
  exact he

theorem planePairOperator_lowDegree (L : ℕ) (q : CountablePairSpace)
    (hq : PairDegreeAtMost L q) :
    planePairOperator q = finitePairOperator
      (∑ p ∈ Finset.range (2*L+1), pairRankOne (planeFiniteBlock L p)) q := by
  let qf := (finitePairEmbedding (L+1)).toContinuousLinearMap.adjoint q
  have he : finitePairEmbedding (L+1) qf = q := pairDegree_exact_finite L q hq
  change planePairOperator q = finitePairEmbedding (L+1)
    ((∑ p ∈ Finset.range (2*L+1), pairRankOne (planeFiniteBlock L p)) qf)
  simp only [LinearMap.sum_apply, pairRankOne, ContinuousLinearMap.coe_coe,
    InnerProductSpace.rankOne_apply, map_sum]
  calc
    _ = planePairOperator (finitePairEmbedding (L+1) qf) := by rw [he]
    _ = ∑ p ∈ Finset.range (2*L+1),
        (inner ℂ (planeFiniteBlock L p) qf) • planeBlockVector (p+1) :=
      planePairOperator_finite_input L qf
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p hp
      by_cases hlow : p+1 ≤ L
      · rw [map_smul, finitePairEmbedding_planeFiniteBlock L p hlow]
      · have hc : inner ℂ (planeFiniteBlock L p) qf = 0 := by
          rw [← planeBlock_inner_finitePair, he]
          exact planeBlock_inner_zero_of_degree L (p+1) q hq (by omega)
        simp [hc]

theorem countablePairFiber_degree (L N : ℕ) (x : countableSector N)
    (hx : CountableDegreeAtMost L x) (A : Finset ℕ) :
    PairDegreeAtMost L (countablePairFiber (countablePairStack N x) A) := by
  intro a ha
  change countableTransitionLinear a.val.2 false
    (countableTransitionLinear a.val.1 false x) A = 0
  rw [countableTransitionLinear_apply]
  by_cases hj : a.val.2 ∈ A
  · simp [hj]
  · rw [ite_eq_left (by simp [hj]), countableFlip_of_not_mem hj,
      countableTransitionLinear_apply]
    by_cases hi : a.val.1 ∈ insert a.val.2 A
    · simp [hi]
    · rw [ite_eq_left (by simp [hi]), countableFlip_of_not_mem hi]
      have hd : L < ∑ i ∈ insert a.val.1 (insert a.val.2 A), i := by
        rw [Finset.sum_insert hi, Finset.sum_insert hj]
        omega
      rw [hx _ hd]
      simp

theorem countablePlane_degree_compression (L N : ℕ) (x : countableSector N)
    (hx : CountableDegreeAtMost L x) :
    countablePairLift N planePairOperator x =
      countablePairLift N (finitePairOperator
        (∑ p ∈ Finset.range (2*L+1), pairRankOne (planeFiniteBlock L p))) x := by
  change (countablePairStack N).adjoint
    (countablePairAmplify planePairOperator (countablePairStack N x)) =
    (countablePairStack N).adjoint
      (countablePairAmplify (finitePairOperator
        (∑ p ∈ Finset.range (2*L+1), pairRankOne (planeFiniteBlock L p)))
          (countablePairStack N x))
  apply congrArg ((countablePairStack N).adjoint)
  ext a A
  exact congrArg (fun q : CountablePairSpace => q a)
    (planePairOperator_lowDegree L (countablePairFiber (countablePairStack N x) A)
      (countablePairFiber_degree L N x hx A))

theorem countablePlane_degree_finite (L N : ℕ) (x : countableSector N)
    (hx : CountableDegreeAtMost L x) :
    (countablePairLift N planePairOperator x : CountableSpace) =
      countableEmbed (L+1) (planeFiniteHamiltonian L (countableRestrict (L+1) x)) := by
  let y := countableRestrict (L+1) x
  have hy : InSector N y := countableRestrict_sector x.property
  have he : countableEmbed (L+1) y = (x : CountableSpace) := countableDegree_exact_finite L x hx
  let Q := ∑ p ∈ Finset.range (2*L+1), pairRankOne (planeFiniteBlock L p)
  calc
    _ = (countablePairLift N (finitePairOperator Q) x : CountableSpace) :=
      congrArg (fun z : countableSector N => (z : CountableSpace))
        (countablePlane_degree_compression L N x hx)
    _ = countableEmbed (L+1) (pairLift Q y) := by
      have h := countablePairLift_finite_embed Q y hy
      have hs : (⟨countableEmbed (L+1) y, countableEmbed_sector hy⟩ : countableSector N) = x :=
        Subtype.ext he
      rw [hs] at h
      exact h
    _ = _ := by rw [← planeFiniteHamiltonian_pairLift]

end VortexGap.Fermion

