import VortexGap.Fermion.CountableSectors
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open Filter
open scoped BigOperators Topology

def CountableDegreeAtMost (L : ℕ) (x : CountableSpace) : Prop :=
  ∀ A : Finset ℕ, L < ∑ i ∈ A, i → x A = 0

theorem occupation_subset_degree_bound (L : ℕ) (A : Finset ℕ)
    (hA : ∑ i ∈ A, i ≤ L) : A ⊆ Finset.range (L+1) := by
  intro i hi
  have h : i ≤ ∑ j ∈ A, j := Finset.single_le_sum (fun j _ => Nat.zero_le j) hi
  exact Finset.mem_range.mpr (by omega)

theorem countableDegree_cutoff (L : ℕ) (x : CountableSpace)
    (hx : CountableDegreeAtMost L x) : countableCutoff (L+1) x = x := by
  ext A
  rw [countableCutoff_coefficient]
  split_ifs with hA
  · rfl
  · exact (hx A (by
      by_contra h
      exact hA (occupation_subset_degree_bound L A (by omega)))).symm

theorem countableDegree_exact_finite (L : ℕ) (x : CountableSpace)
    (hx : CountableDegreeAtMost L x) :
    countableEmbed (L+1) (countableRestrict (L+1) x) = x := by
  rw [countableEmbed_restrict, countableDegree_cutoff L x hx]

theorem countableDegree_sector_exact (L N : ℕ) (x : countableSector N)
    (hx : CountableDegreeAtMost L x) :
    ∃ y : Space (L+1), InSector N y ∧ countableEmbed (L+1) y = (x : CountableSpace) := by
  exact ⟨countableRestrict (L+1) x, countableRestrict_sector x.property,
    countableDegree_exact_finite L x hx⟩

theorem countableCutoff_degree (n : ℕ) (x : CountableSpace) :
    CountableDegreeAtMost (∑ i ∈ Finset.range n, i) (countableCutoff n x) := by
  intro A hA
  rw [countableCutoff_coefficient]
  split_ifs with hs
  · have hle : (∑ i ∈ A, i) ≤ ∑ i ∈ Finset.range n, i :=
      Finset.sum_le_sum_of_subset_of_nonneg hs (by intros; exact Nat.zero_le _)
    omega
  · rfl

theorem countableDegree_closed_extension {N : ℕ} (S : Set CountableSpace)
    (hS : IsClosed S)
    (hdegree : ∀ (L : ℕ) (x : CountableSpace), x ∈ countableSector N →
      CountableDegreeAtMost L x → x ∈ S)
    (x : CountableSpace) (hx : x ∈ countableSector N) : x ∈ S := by
  apply hS.mem_of_tendsto (countableCutoff_tendsto x)
  exact Filter.Eventually.of_forall fun n => hdegree _ _
    (countableCutoff_sector n hx) (countableCutoff_degree n x)
end VortexGap.Fermion
