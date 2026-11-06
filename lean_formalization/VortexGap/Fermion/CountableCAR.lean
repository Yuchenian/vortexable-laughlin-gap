import VortexGap.Fermion.CountableModes

/-! Coordinate CAR proofs adapt the pinned OAI occupation argument (Apache-2.0;
vendor/upstream_audit), now for the constructed bounded countable-mode operators. -/
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped InnerProduct

theorem countableTransition_anticommute_of_ne {i j : ℕ} (hij : i ≠ j) (ε η : Bool) :
    countableTransition i ε * countableTransition j η =
      -(countableTransition j η * countableTransition i ε) := by
  ext x A
  change countableTransition i ε (countableTransition j η x) A =
    -countableTransition j η (countableTransition i ε x) A
  simp only [countableTransition_apply, countableFlip_mem_other hij,
    countableFlip_mem_other (Ne.symm hij), countableSign_flip]
  rw [countableFlip_comm j i A]
  by_cases hi : decide (i ∈ A) = ε <;> by_cases hj : decide (j ∈ A) = η
  · rcases lt_or_gt_of_ne hij with hlt | hgt
    · simp [hi, hj, hlt, not_lt_of_ge (le_of_lt hlt)]
      ring
    · simp [hi, hj, hgt, not_lt_of_ge (le_of_lt hgt)]
      ring
  all_goals simp [hi, hj]

theorem countableTransition_square (j : ℕ) (ε : Bool) :
    countableTransition j ε * countableTransition j ε = 0 := by
  ext x A
  change countableTransition j ε (countableTransition j ε x) A = 0
  simp only [countableTransition_apply, countableFlip_mem_self,
    countableFlip_flip, countableSign_flip_self]
  cases ε <;> by_cases hj : j ∈ A <;> simp [hj]

theorem countableTransition_complement (j : ℕ) (ε : Bool) :
    countableTransition j ε * countableTransition j (!ε) +
      countableTransition j (!ε) * countableTransition j ε = 1 := by
  ext x A
  change countableTransition j ε (countableTransition j (!ε) x) A +
    countableTransition j (!ε) (countableTransition j ε x) A = x A
  simp only [countableTransition_apply, countableFlip_mem_self,
    countableFlip_flip, countableSign_flip_self]
  cases ε <;> by_cases hj : j ∈ A <;> simp [hj, ← mul_assoc]

/-- CAR as an equality of actual bounded operators, with no finite-mode restriction. -/
theorem countableMode_car (i j : ℕ) :
    countableAnnihilateMode i * countableCreateMode j +
      countableCreateMode j * countableAnnihilateMode i = if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    simpa using countableTransition_complement i false
  · rw [ite_eq_right hij, countableTransition_anticommute_of_ne hij false true]
    exact neg_add_cancel _

theorem countableTransition_anticommute (i j : ℕ) (ε : Bool) :
    countableTransition i ε * countableTransition j ε =
      -(countableTransition j ε * countableTransition i ε) := by
  by_cases hij : i = j
  · subst j; simp [countableTransition_square]
  · exact countableTransition_anticommute_of_ne hij ε ε

theorem countableMode_norm_identity (j : ℕ) (x : CountableSpace) :
    ‖countableCreateMode j x‖ ^ 2 + ‖countableAnnihilateMode j x‖ ^ 2 = ‖x‖ ^ 2 := by
  have hc : (countableCreateMode j).adjoint = countableAnnihilateMode j :=
    countableTransition_adjoint j true
  have ha : (countableAnnihilateMode j).adjoint = countableCreateMode j :=
    countableTransition_adjoint j false
  have he : inner ℂ (countableCreateMode j x) (countableCreateMode j x) +
      inner ℂ (countableAnnihilateMode j x) (countableAnnihilateMode j x) = inner ℂ x x := by
    calc
      _ = inner ℂ x ((countableAnnihilateMode j * countableCreateMode j +
          countableCreateMode j * countableAnnihilateMode j) x) := by
        rw [← ContinuousLinearMap.adjoint_inner_right (countableCreateMode j) x (countableCreateMode j x), hc,
          ← ContinuousLinearMap.adjoint_inner_right (countableAnnihilateMode j) x (countableAnnihilateMode j x), ha,
          ← inner_add_right]
        rfl
      _ = _ := by rw [countableMode_car]; simp
  simp only [inner_self_eq_norm_sq_to_K] at he
  exact_mod_cast he

end VortexGap.Fermion

