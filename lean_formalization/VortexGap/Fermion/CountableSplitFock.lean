import VortexGap.Fermion.CountableSplitIndex

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open Filter
open scoped InnerProduct

/-- Completed tensor occupation amplitudes, with environment coordinate first. -/
abbrev CountableSplitSpace := lp (fun _ : Finset ℕ × Finset ℕ => ℂ) 2

def countableSplitKet (AB : Finset ℕ × Finset ℕ) : CountableSplitSpace := lp.single 2 AB 1

theorem countableSplitKet_inner_left (AB : Finset ℕ × Finset ℕ) (x : CountableSplitSpace) :
    inner ℂ (countableSplitKet AB) x = x AB := by
  simp [countableSplitKet, lp.inner_single_left, RCLike.inner_apply]

theorem countableSplitSpace_hasSum (x : CountableSplitSpace) :
    HasSum (fun AB => x AB • countableSplitKet AB) x := by
  simpa only [countableSplitKet, ← lp.single_smul, smul_eq_mul, mul_one]
    using lp.hasSum_single (by norm_num : (2 : ENNReal) ≠ ⊤) x

theorem countableJoinImage_orthonormal : Orthonormal ℂ countableJoinImage := by
  apply orthonormal_iff_ite.mpr
  intro AB CD
  by_cases h : AB = CD
  · subst CD
    rw [ite_eq_left rfl]
    change inner ℂ (countableWord orbitalKet (countableJoinList AB.1 AB.2))
      (countableWord orbitalKet (countableJoinList AB.1 AB.2)) = 1
    exact countableWord_inner_self orbitalKet orbitalKet_orthonormal _
      (countableJoinList_nodup AB.1 AB.2)
  · have hi : countableSplitIndex AB ≠ countableSplitIndex CD :=
      fun hi => h (countableSplitIndex.injective hi)
    rw [countableJoinImage_ket, countableJoinImage_ket, inner_smul_left, inner_smul_right,
      countableKet_inner, if_neg hi, mul_zero, mul_zero, if_neg h]

def countableJoinIsometry : CountableSplitSpace →ₗᵢ[ℂ] CountableSpace :=
  countableJoinImage_orthonormal.orthogonalFamily.linearIsometry

theorem countableJoinIsometry_ket (AB : Finset ℕ × Finset ℕ) :
    countableJoinIsometry (countableSplitKet AB) = countableJoinImage AB := by
  rw [countableJoinIsometry, countableSplitKet, OrthogonalFamily.linearIsometry_apply_single,
    LinearIsometry.toSpanSingleton_apply, one_smul]

theorem countableJoinIsometry_hasSum (x : CountableSplitSpace) :
    HasSum (fun AB => x AB • countableJoinImage AB) (countableJoinIsometry x) := by
  have h := (countableSplitSpace_hasSum x).map
    countableJoinIsometry.toContinuousLinearMap.toAddMonoidHom countableJoinIsometry.continuous
  change HasSum (fun AB => countableJoinIsometry (x AB • countableSplitKet AB))
    (countableJoinIsometry x) at h
  simpa only [map_smul, countableJoinIsometry_ket] using h

theorem countableJoinIsometry_ket_mem_range (S : Finset ℕ) :
    countableKet S ∈ countableJoinIsometry.toLinearMap.range := by
  let AB := countableSplitIndex.symm S
  refine ⟨countableWordSign (countableJoinList AB.1 AB.2) • countableSplitKet AB, ?_⟩
  change countableJoinIsometry (_ • countableSplitKet AB) = countableKet S
  rw [map_smul, countableJoinIsometry_ket, countableJoinImage_ket, smul_smul,
    countableWordSign_sq, one_smul]
  exact congrArg countableKet (countableSplitIndex.apply_symm_apply S)

/-- Surjectivity follows from actual signed occupation images and Hilbert completion. -/
theorem countableJoinIsometry_surjective : Function.Surjective countableJoinIsometry := by
  intro x
  change x ∈ countableJoinIsometry.toLinearMap.range
  have hc : IsClosed (countableJoinIsometry.toLinearMap.range : Set CountableSpace) :=
    countableJoinIsometry.isometry.isClosedEmbedding.isClosed_range
  apply hc.mem_of_tendsto (countableSpace_hasSum x)
  apply Eventually.of_forall
  intro s
  apply countableJoinIsometry.toLinearMap.range.sum_mem
  intro S hS
  exact countableJoinIsometry.toLinearMap.range.smul_mem (x S) (countableJoinIsometry_ket_mem_range S)

def countableFockJoin : CountableSplitSpace ≃ₗᵢ[ℂ] CountableSpace :=
  LinearIsometryEquiv.ofSurjective countableJoinIsometry countableJoinIsometry_surjective

def countableFockSplit : CountableSpace ≃ₗᵢ[ℂ] CountableSplitSpace := countableFockJoin.symm

theorem countableFockJoin_apply (x : CountableSplitSpace) :
    countableFockJoin x = countableJoinIsometry x := rfl

theorem countableFockJoin_ket (AB : Finset ℕ × Finset ℕ) :
    countableFockJoin (countableSplitKet AB) = countableJoinImage AB :=
  countableJoinIsometry_ket AB

theorem countableFockSplit_image (AB : Finset ℕ × Finset ℕ) :
    countableFockSplit (countableJoinImage AB) = countableSplitKet AB := by
  rw [← countableFockJoin_ket]
  exact countableFockJoin.symm_apply_apply _

theorem countableFockSplit_ket_index (AB : Finset ℕ × Finset ℕ) :
    countableFockSplit (countableKet (countableSplitIndex AB)) =
      countableWordSign (countableJoinList AB.1 AB.2) • countableSplitKet AB := by
  apply countableFockJoin.injective
  rw [show countableFockJoin (countableFockSplit _) = _ from countableFockJoin.apply_symm_apply _,
    map_smul, countableFockJoin_ket, countableJoinImage_ket, smul_smul,
    countableWordSign_sq, one_smul]

theorem countableFockSplit_coefficient (x : CountableSpace) (AB : Finset ℕ × Finset ℕ) :
    countableFockSplit x AB = inner ℂ (countableJoinImage AB) x := by
  rw [← countableSplitKet_inner_left]
  rw [← countableFockJoin.inner_map_map, countableFockJoin_ket]
  exact congrArg (inner ℂ (countableJoinImage AB)) (countableFockJoin.apply_symm_apply x)

theorem countableFockJoin_norm (x : CountableSplitSpace) : ‖countableFockJoin x‖ = ‖x‖ :=
  countableFockJoin.norm_map x

theorem countableFockSplit_norm (x : CountableSpace) : ‖countableFockSplit x‖ = ‖x‖ :=
  countableFockSplit.norm_map x

end VortexGap.Fermion
