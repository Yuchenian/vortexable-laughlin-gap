import VortexGap.Fermion.CountableCompatibility

/-! Exact actions on occupation kets. The creation-coordinate argument follows the
pinned finite occupation proof (Apache-2.0; vendor/upstream_audit). -/
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion

theorem countableKet_apply (A B : Finset ℕ) : countableKet A B = if B = A then 1 else 0 := by
  rw [← countableKet_inner_left B (countableKet A), countableKet_inner]

theorem countableCreateMode_ket (j : ℕ) (A : Finset ℕ) (hj : j ∉ A) :
    countableCreateMode j (countableKet A) = countableSign j A • countableKet (insert j A) := by
  have hs : countableSign j (insert j A) = countableSign j A := by
    simpa using countableSign_insert j hj
  ext B
  change countableTransition j true (countableKet A) B = countableSign j A * countableKet (insert j A) B
  by_cases hB : j ∈ B
  · by_cases he : B.erase j = A
    · have hBA : B = insert j A := by rw [← he, Finset.insert_erase hB]
      subst B
      simp [countableTransition_apply, countableKet_apply, hj, hs]
    · have hBA : B ≠ insert j A := by
        intro h
        subst B
        simp [hj] at he
      simp [countableTransition_apply, countableKet_apply, hB, he, hBA]
  · have hBA : B ≠ insert j A := by
      intro h
      rw [h] at hB
      simp at hB
    simp [countableTransition_apply, countableKet_apply, hB, hBA]

theorem countableAnnihilateMode_ket (j : ℕ) (A : Finset ℕ) (hj : j ∈ A) :
    countableAnnihilateMode j (countableKet A) = countableSign j A • countableKet (A.erase j) := by
  have hs : countableSign j (A.erase j) = countableSign j A := by
    simpa only [countableFlip_of_mem hj] using countableSign_flip_self j A
  ext B
  change countableTransition j false (countableKet A) B = countableSign j A * countableKet (A.erase j) B
  by_cases hB : j ∈ B
  · have hBA : B ≠ A.erase j := by
      intro h
      rw [h] at hB
      simpa using hB
    simp [countableTransition_apply, countableKet_apply, hB, hBA]
  · by_cases he : insert j B = A
    · have hBA : B = A.erase j := by rw [← he, Finset.erase_insert hB]
      subst B
      simp [countableTransition_apply, countableKet_apply, Finset.insert_erase hj, hs]
    · have hBA : B ≠ A.erase j := by
        intro h
        subst B
        exact he (Finset.insert_erase hj)
      simp [countableTransition_apply, countableKet_apply, hB, he, hBA]

theorem countableAnnihilateMode_ket_of_not_mem (j : ℕ) (A : Finset ℕ) (hj : j ∉ A) :
    countableAnnihilateMode j (countableKet A) = 0 := by
  ext B
  by_cases hB : j ∈ B
  · simp [countableAnnihilateMode, countableTransition_apply, hB]
  · have he : insert j B ≠ A := by
      intro h
      apply hj
      rw [← h]
      simp
    simp [countableAnnihilateMode, countableTransition_apply, countableKet_apply, hB, he]

theorem countableCreateMode_ket_of_mem (j : ℕ) (A : Finset ℕ) (hj : j ∈ A) :
    countableCreateMode j (countableKet A) = 0 := by
  ext B
  by_cases hB : j ∈ B
  · have he : B.erase j ≠ A := by
      intro h
      have hn := Finset.notMem_erase j B
      rw [h] at hn
      exact hn hj
    simp [countableCreateMode, countableTransition_apply, countableKet_apply, hB, he]
  · simp [countableCreateMode, countableTransition_apply, hB]

/-- Sharp induced operator norm on the full countable-mode Fock space. -/
theorem countableTransition_opNorm_eq_one (j : ℕ) (ε : Bool) : ‖countableTransition j ε‖ = 1 := by
  apply le_antisymm (countableTransition_opNorm_le j ε)
  cases ε
  · have h := (countableAnnihilateMode j).le_opNorm (countableKet {j})
    rw [countableAnnihilateMode_ket j {j} (by simp)] at h
    simpa only [norm_smul, countableSign_norm, countableKet_norm, one_mul, mul_one] using h
  · have h := (countableCreateMode j).le_opNorm (countableKet ∅)
    rw [countableCreateMode_ket j ∅ (by simp)] at h
    simpa only [norm_smul, countableSign_norm, countableKet_norm, one_mul, mul_one] using h

end VortexGap.Fermion

