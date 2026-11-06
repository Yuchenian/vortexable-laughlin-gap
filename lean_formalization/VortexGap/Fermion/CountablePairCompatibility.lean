import VortexGap.Fermion.CountablePairSpace

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped InnerProduct Topology

def finitePairEmbeddingLinear (n : ℕ) : PairSpace n →ₗ[ℂ] CountablePairSpace :=
  countablePairCoordinates.toLinearMap.comp ((countableEmbed n).toLinearMap.comp pairEmbed)

theorem finitePairEmbeddingLinear_norm {n : ℕ} (p : PairSpace n) :
    ‖finitePairEmbeddingLinear n p‖ = ‖p‖ := by
  change ‖countablePairCoordinates (countableEmbed n (pairEmbed p))‖ = _
  rw [countablePairCoordinates_norm_on_sector (countableEmbed_sector (pairEmbed_sector p)),
    (countableEmbed n).norm_map, pairEmbed_norm]

/-- The finite pair coordinates embedded in the completed countable pair space. -/
def finitePairEmbedding (n : ℕ) : PairSpace n →ₗᵢ[ℂ] CountablePairSpace where
  toLinearMap := finitePairEmbeddingLinear n
  norm_map' := finitePairEmbeddingLinear_norm

theorem finitePairEmbedding_intertwine {n : ℕ} (p : PairSpace n) :
    countablePairEmbedding (finitePairEmbedding n p) = countableEmbed n (pairEmbed p) :=
  countablePairEmbedding_coordinates (countableEmbed_sector (pairEmbed_sector p))

theorem pairOccupation_nat {n : ℕ} (a : PairIndex n) :
    countablePairOccupation (pairIndexNat a) = occupationIndex (pairOccupation a) := by
  simp [countablePairOccupation, pairIndexNat, occupationIndex, pairOccupation]

theorem finitePairEmbedding_coefficient {n : ℕ} (p : PairSpace n) (a : PairIndex n) :
    finitePairEmbedding n p (pairIndexNat a) = p a := by
  change countablePairCoordinates (countableEmbed n (pairEmbed p)) (pairIndexNat a) = _
  rw [countablePairCoordinates_coefficient, pairOccupation_nat]
  change countableEmbedLinear n (pairEmbed p) (occupationIndex (pairOccupation a)) = _
  rw [countableEmbedLinear_coefficient, pairEmbed_coefficient]

theorem finitePairEmbedding_outside {n : ℕ} (p : PairSpace n) (a : CountablePairIndex)
    (ha : n ≤ a.val.2) : finitePairEmbedding n p a = 0 := by
  change countablePairCoordinates (countableEmbed n (pairEmbed p)) a = _
  rw [countablePairCoordinates_coefficient]
  apply countableEmbed_outside
  intro h
  have hj := h (show a.val.2 ∈ countablePairOccupation a by simp [countablePairOccupation])
  have := Finset.mem_range.mp hj
  omega

theorem finitePairEmbedding_basis {n : ℕ} (a : PairIndex n) :
    finitePairEmbedding n (pairBasis a) = lp.single 2 (pairIndexNat a) 1 := by
  apply countablePairEmbedding.injective
  rw [finitePairEmbedding_intertwine, countablePairEmbedding_single, one_smul]
  have h : pairEmbed (pairBasis a) = pairKet a := by
    simp [pairEmbed, pairBasis]
  rw [h, countablePairKet_embed]

theorem finitePairEmbedding_approximation (p : CountablePairSpace) (ε : ℝ) (hε : 0 < ε) :
    ∃ n, ∃ q : PairSpace n, ‖finitePairEmbedding n q - p‖ < ε := by
  obtain ⟨n, y, hy, he⟩ := countableSector_finite_approximation
    ⟨countablePairEmbedding p, countablePairEmbedding_sector p⟩ ε hε
  obtain ⟨q, rfl⟩ := (pairEmbed_range_iff y).mpr hy
  refine ⟨n, q, ?_⟩
  rw [← countablePairEmbedding.norm_map, map_sub, finitePairEmbedding_intertwine]
  exact he

theorem finitePairEmbedding_dense : Dense (⋃ n, Set.range (finitePairEmbedding n)) := by
  intro p
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨n, q, hq⟩ := finitePairEmbedding_approximation p ε hε
  exact ⟨finitePairEmbedding n q, Set.mem_iUnion.mpr ⟨n, ⟨q, rfl⟩⟩,
    by simpa only [dist_eq_norm, norm_sub_rev p] using hq⟩

end VortexGap.Fermion

