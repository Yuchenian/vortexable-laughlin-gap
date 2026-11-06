import VortexGap.Reference.PlanarHamiltonian
import VortexGap.Geometry.PlaneResolution
import VortexGap.Fermion.CountablePairLiftCompatibility
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped BigOperators InnerProduct ENNReal

theorem finitePairEmbedding_adjoint_planeBlock (L p : ℕ) :
    (finitePairEmbedding (L+1)).toContinuousLinearMap.adjoint (planeBlockVector (p+1)) =
      planeFiniteBlock L p := by
  ext a
  have h := ContinuousLinearMap.adjoint_inner_right
    (finitePairEmbedding (L+1)).toContinuousLinearMap (pairBasis a) (planeBlockVector (p+1))
  simp only [LinearIsometry.coe_toContinuousLinearMap] at h
  rw [finitePairEmbedding_basis] at h
  simpa [pairBasis, planeFiniteBlock,
    EuclideanSpace.inner_single_left, lp.inner_single_left] using h

theorem planeBlock_inner_finitePair (L p : ℕ) (q : PairSpace (L+1)) :
    inner ℂ (planeBlockVector (p+1)) (finitePairEmbedding (L+1) q) =
      inner ℂ (planeFiniteBlock L p) q := by
  rw [← finitePairEmbedding_adjoint_planeBlock]
  exact (ContinuousLinearMap.adjoint_inner_left
    (finitePairEmbedding (L+1)).toContinuousLinearMap q (planeBlockVector (p+1))).symm

theorem planeFiniteBlock_zero (L p : ℕ) (hp : 2*L+1 ≤ p) : planeFiniteBlock L p = 0 := by
  ext a
  change planeBlockVector (p+1) (pairIndexNat a) = 0
  apply planeBlockVector_off_block
  have hi := a.val.1.isLt
  have hj := a.val.2.isLt
  dsimp [pairIndexNat]
  omega

theorem planeBlockCoordinates_finitePair (L : ℕ) (q : PairSpace (L+1)) :
    planeBlockSynthesis.toContinuousLinearMap.adjoint (finitePairEmbedding (L+1) q) =
      ∑ p ∈ Finset.range (2*L+1),
        (inner ℂ (planeFiniteBlock L p) q) • (lp.single (E := fun _ : ℕ => ℂ) 2 p (1 : ℂ)) := by
  let z : CountableOrbital := planeBlockSynthesis.toContinuousLinearMap.adjoint
    (finitePairEmbedding (L+1) q)
  have hz (k : ℕ) (hk : k ∉ Finset.range (2*L+1)) : z k = 0 := by
    change planeBlockSynthesis.toContinuousLinearMap.adjoint (finitePairEmbedding (L+1) q) k = 0
    rw [planeBlockSynthesis_adjoint_coordinate, planeBlock_inner_finitePair,
      planeFiniteBlock_zero L k (by simpa only [Finset.mem_range, not_lt] using hk)]
    simp
  have hs := lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) z
  calc
    _ = ∑' k, (lp.single (E := fun _ : ℕ => ℂ) 2 k (z k) : CountableOrbital) := hs.tsum_eq.symm
    _ = ∑ k ∈ Finset.range (2*L+1), (lp.single (E := fun _ : ℕ => ℂ) 2 k (z k) : CountableOrbital) :=
      tsum_eq_sum (fun k hk => by rw [hz k hk]; simp)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      change lp.single (E := fun _ : ℕ => ℂ) 2 k
        (planeBlockSynthesis.toContinuousLinearMap.adjoint (finitePairEmbedding (L+1) q) k) = _
      rw [planeBlockSynthesis_adjoint_coordinate, planeBlock_inner_finitePair]
      simp [← lp.single_smul]

theorem planePairOperator_finite_input (L : ℕ) (q : PairSpace (L+1)) :
    planePairOperator (finitePairEmbedding (L+1) q) =
      ∑ p ∈ Finset.range (2*L+1),
        (inner ℂ (planeFiniteBlock L p) q) • planeBlockVector (p+1) := by
  rw [planePairOperator_eq_block_projection, ContinuousLinearMap.comp_apply,
    planeBlockCoordinates_finitePair, map_sum]
  simp only [map_smul, LinearIsometry.coe_toContinuousLinearMap, planeBlockSynthesis_single]

theorem planePairOperator_finite_compression (L : ℕ) (q : PairSpace (L+1)) :
    (finitePairEmbedding (L+1)).toContinuousLinearMap.adjoint
      (planePairOperator (finitePairEmbedding (L+1) q)) =
      (∑ p ∈ Finset.range (2*L+1), pairRankOne (planeFiniteBlock L p)) q := by
  rw [planePairOperator_finite_input, map_sum]
  simp only [map_smul, finitePairEmbedding_adjoint_planeBlock, LinearMap.sum_apply]
  rfl
end VortexGap.Fermion

