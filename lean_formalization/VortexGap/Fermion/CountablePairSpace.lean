import VortexGap.Fermion.CountablePairModes

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open Filter
open scoped InnerProduct BigOperators Topology

theorem countablePairKet_orthonormal : Orthonormal ℂ countablePairKet :=
  orthonormal_iff_ite.mpr countablePairKet_inner

/-- The completed pair Hilbert space embeds isometrically via the concrete pair kets. -/
def countablePairEmbedding : CountablePairSpace →ₗᵢ[ℂ] CountableSpace :=
  countablePairKet_orthonormal.orthogonalFamily.linearIsometry

theorem countablePairEmbedding_hasSum (p : CountablePairSpace) :
    HasSum (fun a => p a • countablePairKet a) (countablePairEmbedding p) := by
  simpa only [LinearIsometry.toSpanSingleton_apply, countablePairEmbedding] using
    countablePairKet_orthonormal.orthogonalFamily.hasSum_linearIsometry p

theorem countablePairEmbedding_single (a : CountablePairIndex) (z : ℂ) :
    countablePairEmbedding (lp.single 2 a z) = z • countablePairKet a := by
  exact countablePairKet_orthonormal.orthogonalFamily.linearIsometry_apply_single z

theorem countablePairEmbedding_coefficient (p : CountablePairSpace) (a : CountablePairIndex) :
    countablePairEmbedding p (countablePairOccupation a) = p a := by
  calc
    _ = inner ℂ (countablePairKet a) (countablePairEmbedding p) := by
      rw [countablePairKet_occupation, countableKet_inner_left]
    _ = inner ℂ (countablePairEmbedding (lp.single 2 a 1)) (countablePairEmbedding p) := by
      rw [countablePairEmbedding_single, one_smul]
    _ = inner ℂ (lp.single 2 a 1) p := countablePairEmbedding.inner_map_map _ _
    _ = _ := by simp [lp.inner_single_left, RCLike.inner_apply]

theorem countablePairEmbedding_sector (p : CountablePairSpace) :
    countablePairEmbedding p ∈ countableSector 2 := by
  apply (countableSector_isClosed 2).mem_of_tendsto (countablePairEmbedding_hasSum p)
  exact Eventually.of_forall fun s => (countableSector 2).sum_mem fun a ha =>
    (countableSector 2).smul_mem (p a) (countablePairKet_sector a)

theorem countablePairOccupation_exists (A : Finset ℕ) (hA : A.card = 2) :
    ∃ a : CountablePairIndex, countablePairOccupation a = A := by
  obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp hA
  rcases lt_or_gt_of_ne hij with h | h
  · exact ⟨⟨(i, j), h⟩, rfl⟩
  · refine ⟨⟨(j, i), h⟩, ?_⟩
    exact Finset.pair_comm j i

/-- Actual Hilbert adjoint, giving the coordinates of the two-particle component. -/
def countablePairCoordinates : CountableSpace →L[ℂ] CountablePairSpace :=
  countablePairEmbedding.toContinuousLinearMap.adjoint

theorem countablePairCoordinates_coefficient (x : CountableSpace) (a : CountablePairIndex) :
    countablePairCoordinates x a = x (countablePairOccupation a) := by
  calc
    _ = inner ℂ (lp.single 2 a 1) (countablePairCoordinates x) := by
      simp [lp.inner_single_left, RCLike.inner_apply]
    _ = inner ℂ (countablePairEmbedding (lp.single 2 a 1)) x :=
      ContinuousLinearMap.adjoint_inner_right _ _ _
    _ = _ := by
      rw [countablePairEmbedding_single, one_smul, countablePairKet_occupation, countableKet_inner_left]

theorem countablePairCoordinates_embed (p : CountablePairSpace) :
    countablePairCoordinates (countablePairEmbedding p) = p := by
  ext a
  rw [countablePairCoordinates_coefficient, countablePairEmbedding_coefficient]

/-- All of the actual two-particle sector is covered, including infinite-support states. -/
theorem countablePairEmbedding_coordinates {x : CountableSpace} (hx : x ∈ countableSector 2) :
    countablePairEmbedding (countablePairCoordinates x) = x := by
  ext A
  by_cases hA : A.card = 2
  · obtain ⟨a, rfl⟩ := countablePairOccupation_exists A hA
    rw [countablePairEmbedding_coefficient, countablePairCoordinates_coefficient]
  · rw [countablePairEmbedding_sector _ A hA, hx A hA]

theorem countablePairEmbedding_range :
    Set.range countablePairEmbedding = (countableSector 2 : Set CountableSpace) := by
  ext x
  constructor
  · rintro ⟨p, rfl⟩; exact countablePairEmbedding_sector p
  · intro hx; exact ⟨countablePairCoordinates x, countablePairEmbedding_coordinates hx⟩

theorem countablePairCoordinates_norm_on_sector {x : CountableSpace}
    (hx : x ∈ countableSector 2) : ‖countablePairCoordinates x‖ = ‖x‖ := by
  rw [← countablePairEmbedding.norm_map, countablePairEmbedding_coordinates hx]

end VortexGap.Fermion

