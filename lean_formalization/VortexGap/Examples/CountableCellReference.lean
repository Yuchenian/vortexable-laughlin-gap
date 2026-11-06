import VortexGap.Transfer.CountableFiniteFrame
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped InnerProduct ComplexOrder

theorem countableNumberMode_apply (j : ℕ) (x : CountableSpace) (A : Finset ℕ) :
    countableCreateMode j (countableAnnihilateMode j x) A =
      if j ∈ A then x A else 0 := by
  simp only [countableTransition_apply, countableFlip_mem_self,
    countableFlip_flip, countableSign_flip_self]
  by_cases hj : j ∈ A <;> simp [hj, ← mul_assoc]

theorem countablePairMode_occupation (a : CountablePairIndex)
    (x : CountableSpace) (A : Finset ℕ) :
    ((countablePairMode a).adjoint * countablePairMode a) x A =
      if a.val.1 ∈ A ∧ a.val.2 ∈ A then x A else 0 := by
  rw [countablePairMode_adjoint]
  change countableCreateMode a.val.1
    (countableCreateMode a.val.2 (countableAnnihilateMode a.val.2
      (countableAnnihilateMode a.val.1 x))) A = _
  simp only [countableTransition_apply, countableFlip_mem_other (ne_of_lt a.property),
    countableFlip_mem_other (ne_of_gt a.property), countableFlip_mem_self,
    countableFlip_flip, countableSign_flip_self, countableSign_flip]
  by_cases hi : a.val.1 ∈ A <;> by_cases hj : a.val.2 ∈ A <;>
    simp [hi, hj, a.property, not_lt_of_gt a.property, ← mul_assoc]

theorem countableModePairLift_apply (a : CountablePairIndex) (N : ℕ)
    (x : countableSector N) (A : Finset ℕ) :
    (countablePairLift N (InnerProductSpace.rankOne ℂ
      (lp.single 2 a 1) (lp.single 2 a 1)) x : CountableSpace) A =
      if a.val.1 ∈ A ∧ a.val.2 ∈ A then x.val A else 0 := by
  rcases N with _ | N
  · simp only [countablePairLift_zero_sector, zero_apply, ZeroMemClass.coe_zero, lp.coeFn_zero,
      Pi.zero_apply]
    split_ifs with h
    · exact (x.property A (by have := Finset.card_pos.mpr ⟨a.val.1, h.1⟩; omega)).symm
    · rfl
  rcases N with _ | N
  · have hz := countablePairLift_one_sector (InnerProductSpace.rankOne ℂ
        (lp.single 2 a 1) (lp.single 2 a 1))
    rw [hz]
    change 0 = _
    split_ifs with h
    · have hsub : countablePairOccupation a ⊆ A := by
        simpa only [countablePairOccupation, Finset.insert_subset_iff, Finset.singleton_subset_iff] using h
      have hh := Finset.card_le_card hsub
      rw [countablePairOccupation_card] at hh
      exact (x.property A (by omega)).symm
    · rfl
  rw [← countableWedge_basis a, countablePairLift_wedge_rankOne,
    countableCreate_ket, countableCreate_ket, countableAnnihilate_ket, countableAnnihilate_ket]
  have h := countablePairMode_occupation a x A
  rw [countablePairMode_adjoint] at h
  exact h

theorem countableModePairLift_idempotent (a : CountablePairIndex) (N : ℕ) :
    let H := countablePairLift N (InnerProductSpace.rankOne ℂ
      (lp.single 2 a 1) (lp.single 2 a 1))
    H*H = H := by
  dsimp only
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  ext A
  simp only [mul_apply_eq_comp, countableModePairLift_apply]
  split_ifs <;> rfl

theorem countableModePairLift_gap (a : CountablePairIndex) (N : ℕ) :
    let H := countablePairLift N (InnerProductSpace.rankOne ℂ
      (lp.single 2 a 1) (lp.single 2 a 1))
    (H*H - (1 : ℂ) • H).IsPositive := by
  let H := countablePairLift N (InnerProductSpace.rankOne ℂ
    (lp.single 2 a 1) (lp.single 2 a 1))
  change (H*H - (1 : ℂ) • H).IsPositive
  have hh : H*H = H := countableModePairLift_idempotent a N
  have hz : H*H - (1 : ℂ) • H = 0 := by rw [hh]; module
  rw [hz]
  exact ContinuousLinearMap.isPositive_zero
end VortexGap.Fermion
