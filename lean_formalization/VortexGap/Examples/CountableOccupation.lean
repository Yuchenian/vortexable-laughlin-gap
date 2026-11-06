import VortexGap.Fermion.CountableSectors

noncomputable section
set_option autoImplicit false
namespace VortexGap.Examples
open Fermion
open scoped InnerProduct

/-- A two-particle state with a relative complex phase and arbitrarily high orbitals. -/
def countablePairTest (j : ℕ) : CountableSpace :=
  countableKet {0, j + 1} + Complex.I • countableKet {0, j + 2}

theorem countable_cutoff_ket (n : ℕ) (A : Finset ℕ) :
    countableCutoff n (countableKet A) =
      if A ⊆ Finset.range n then countableKet A else 0 := by
  ext B
  rw [countableCutoff_coefficient]
  by_cases h : B = A
  · subst B
    by_cases hs : A ⊆ Finset.range n <;> simp [hs]
  · have hz : countableKet A B = 0 := lp.single_apply_ne 2 A 1 h
    by_cases hs : A ⊆ Finset.range n <;>
      by_cases ht : B ⊆ Finset.range n <;> simp [hs, ht, hz]

theorem countablePairTest_pairs_ne (j : ℕ) :
    ({0, j + 1} : Finset ℕ) ≠ {0, j + 2} := by
  intro h
  have hj : j + 1 ∈ ({0, j + 2} : Finset ℕ) := by rw [← h]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hj
  omega

theorem countablePairTest_sector (j : ℕ) : countablePairTest j ∈ countableSector 2 := by
  have h₁ : ({0, j + 1} : Finset ℕ).card = 2 := by simp
  have h₂ : ({0, j + 2} : Finset ℕ).card = 2 := by simp
  exact (countableSector 2).add_mem
    (by simpa only [h₁] using countableKet_sector ({0, j + 1} : Finset ℕ))
    ((countableSector 2).smul_mem Complex.I
      (by simpa only [h₂] using countableKet_sector ({0, j + 2} : Finset ℕ)))

theorem countablePairTest_norm_sq (j : ℕ) : ‖countablePairTest j‖ ^ 2 = 2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  simp only [countablePairTest, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, countableKet_inner]
  norm_num [countablePairTest_pairs_ne, (countablePairTest_pairs_ne j).symm]

theorem countablePairTest_cutoff (j : ℕ) :
    countableCutoff (j + 2) (countablePairTest j) = countableKet {0, j + 1} := by
  have h₁ : ({0, j + 1} : Finset ℕ) ⊆ Finset.range (j + 2) := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl <;> simp
  have h₂ : ¬ ({0, j + 2} : Finset ℕ) ⊆ Finset.range (j + 2) := by
    intro h
    have := h (by simp : j + 2 ∈ ({0, j + 2} : Finset ℕ))
    simpa using this
  simp [countablePairTest, map_add, map_smul, countable_cutoff_ket, h₁, h₂]

theorem countablePairTest_residual_norm (j : ℕ) :
    ‖countablePairTest j - countableCutoff (j + 2) (countablePairTest j)‖ = 1 := by
  rw [countablePairTest_cutoff]
  simp [countablePairTest, add_sub_cancel_left, norm_smul, countableKet_norm]

theorem countablePairTest_reconstruct (j : ℕ) :
    countableEmbed (j + 3) (countableRestrict (j + 3) (countablePairTest j)) =
      countablePairTest j := by
  have h₁ : ({0, j + 1} : Finset ℕ) ⊆ Finset.range (j + 3) := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl <;> simp
  have h₂ : ({0, j + 2} : Finset ℕ) ⊆ Finset.range (j + 3) := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl <;> simp
  rw [countableEmbed_restrict]
  simp [countablePairTest, map_add, map_smul, countable_cutoff_ket, h₁, h₂]

theorem countablePairTest_nonzero (j : ℕ) : countablePairTest j ≠ 0 := by
  intro h
  have := countablePairTest_norm_sq j
  simp [h] at this

/-- Each finite cutoff omits a genuine normalized occupation state. -/
theorem countableCutoff_ne_one (n : ℕ) : countableCutoff n ≠ 1 := by
  intro h
  have hn : ¬ ({n} : Finset ℕ) ⊆ Finset.range n := by simp
  have hz := congrArg (fun T : CountableSpace →L[ℂ] CountableSpace => T (countableKet {n})) h
  rw [countable_cutoff_ket, if_neg hn] at hz
  have he := congrArg norm hz
  simp only [norm_zero, ContinuousLinearMap.one_apply, countableKet_norm] at he
  norm_num at he

end VortexGap.Examples

