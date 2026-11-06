import VortexGap.Fermion.CountableBasis
import VortexGap.Examples.CountableOccupation

noncomputable section
set_option autoImplicit false
namespace VortexGap.Examples
open Fermion

theorem countable_pair_annihilate_low (j : ℕ) :
    countableAnnihilateMode 0 (countablePairTest j) =
      countableKet {j + 1} + Complex.I • countableKet {j + 2} := by
  rw [countablePairTest, map_add, map_smul,
    countableAnnihilateMode_ket 0 {0, j + 1} (by simp),
    countableAnnihilateMode_ket 0 {0, j + 2} (by simp)]
  simp [countableSign]

theorem countable_pair_annihilate_high (j : ℕ) :
    countableAnnihilateMode (j + 2) (countablePairTest j) =
      (-Complex.I) • countableKet {0} := by
  have hj : j + 2 ∉ ({0, j + 1} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  rw [countablePairTest, map_add, map_smul,
    countableAnnihilateMode_ket_of_not_mem (j + 2) {0, j + 1} hj,
    countableAnnihilateMode_ket (j + 2) {0, j + 2} (by simp)]
  simp [countableSign, Finset.filter_insert, Finset.filter_singleton,
    Finset.erase_insert, Finset.erase_insert_of_ne, smul_smul]

theorem countable_pair_annihilate_high_norm (j : ℕ) :
    ‖countableAnnihilateMode (j + 2) (countablePairTest j)‖ = 1 := by
  rw [countable_pair_annihilate_high]
  simp [norm_smul, countableKet_norm]

theorem countable_pair_create_high (j : ℕ) :
    countableCreateMode (j + 2) (countablePairTest j) =
      countableKet (insert (j + 2) {0, j + 1}) := by
  have hj : j + 2 ∉ ({0, j + 1} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  rw [countablePairTest, map_add, map_smul,
    countableCreateMode_ket (j + 2) {0, j + 1} hj,
    countableCreateMode_ket_of_mem (j + 2) {0, j + 2} (by simp)]
  simp [countableSign, Finset.filter_insert, Finset.filter_singleton]

theorem countable_pair_create_three_particles (j : ℕ) :
    countableCreateMode (j + 2) (countablePairTest j) ∈ countableSector 3 ∧
      ‖countableCreateMode (j + 2) (countablePairTest j)‖ = 1 := by
  constructor
  · exact countableCreateMode_sector (j + 2) (countablePairTest_sector j)
  · rw [countable_pair_create_high]
    exact countableKet_norm _

theorem countable_pair_ordered_annihilation (j : ℕ) :
    countableAnnihilateMode (j + 1) (countableAnnihilateMode 0 (countablePairTest j)) =
      countableKet ∅ := by
  have hj : j + 1 ∉ ({j + 2} : Finset ℕ) := by simp
  rw [countable_pair_annihilate_low, map_add, map_smul,
    countableAnnihilateMode_ket (j + 1) {j + 1} (by simp),
    countableAnnihilateMode_ket_of_not_mem (j + 1) {j + 2} hj]
  simp [countableSign, Finset.filter_singleton]

theorem countable_pair_reversed_annihilation (j : ℕ) :
    countableAnnihilateMode 0 (countableAnnihilateMode (j + 1) (countablePairTest j)) =
      -countableKet ∅ := by
  have h := congrArg (fun T : CountableSpace →L[ℂ] CountableSpace => T (countablePairTest j))
    (countableTransition_anticommute 0 (j + 1) false)
  change countableAnnihilateMode 0 (countableAnnihilateMode (j + 1) (countablePairTest j)) =
    -(countableAnnihilateMode (j + 1) (countableAnnihilateMode 0 (countablePairTest j))) at h
  rw [countable_pair_ordered_annihilation] at h
  exact h

/-- Creation into an excluded orbital is genuinely nonzero before applying the cutoff. -/
theorem countable_creation_outside_cutoff (n : ℕ) :
    countableCutoff n (countableCreateMode n (countableKet ∅)) = 0 ∧
      countableCreateMode n (countableKet ∅) ≠ 0 := by
  have h : countableCreateMode n (countableKet ∅) = countableKet {n} := by
    rw [countableCreateMode_ket n ∅ (by simp)]
    simp [countableSign]
  rw [h]
  constructor
  · rw [countable_cutoff_ket]
    simp
  · intro hz
    have hn := countableKet_norm ({n} : Finset ℕ)
    rw [hz] at hn
    simp at hn

end VortexGap.Examples

