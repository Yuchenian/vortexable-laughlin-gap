import VortexGap.Fermion.CountableWordOperators
import Mathlib.Logic.Equiv.Nat
import Mathlib.Data.Finset.Sum

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion

/-- Even modes are environmental, odd modes are system modes. -/
def countableSplitIndex : (Finset ℕ × Finset ℕ) ≃ Finset ℕ :=
  Finset.sumEquiv.toEquiv.symm.trans Equiv.natSumNatEquivNat.finsetCongr

def countableJoinList (A B : Finset ℕ) : List ℕ :=
  (A.sort (· ≤ ·)).map (fun j => Equiv.natSumNatEquivNat (Sum.inl j)) ++
    (B.sort (· ≤ ·)).map (fun j => Equiv.natSumNatEquivNat (Sum.inr j))

theorem countableSplitIndex_apply (A B : Finset ℕ) :
    countableSplitIndex (A,B) = (A.disjSum B).map Equiv.natSumNatEquivNat.toEmbedding := rfl

theorem countableSplitIndex_card (A B : Finset ℕ) :
    (countableSplitIndex (A,B)).card = A.card + B.card := by
  simp [countableSplitIndex_apply]

theorem countableSplitIndex_mem_env (j : ℕ) (A B : Finset ℕ) :
    Equiv.natSumNatEquivNat (Sum.inl j) ∈ countableSplitIndex (A,B) ↔ j ∈ A := by
  simp [countableSplitIndex_apply]

theorem countableSplitIndex_mem_sys (j : ℕ) (A B : Finset ℕ) :
    Equiv.natSumNatEquivNat (Sum.inr j) ∈ countableSplitIndex (A,B) ↔ j ∈ B := by
  simp [countableSplitIndex_apply]

theorem countableJoinList_length (A B : Finset ℕ) :
    (countableJoinList A B).length = A.card + B.card := by
  simp [countableJoinList]

theorem countableJoinList_nodup (A B : Finset ℕ) : (countableJoinList A B).Nodup := by
  apply List.nodup_append'.mpr
  refine ⟨List.Nodup.map (Equiv.natSumNatEquivNat.injective.comp Sum.inl_injective)
    (Finset.sort_nodup _ _),
    List.Nodup.map (Equiv.natSumNatEquivNat.injective.comp Sum.inr_injective)
    (Finset.sort_nodup _ _), ?_⟩
  rw [List.disjoint_left]
  intro n hn hm
  rcases List.mem_map.mp hn with ⟨i, hi, he⟩
  rcases List.mem_map.mp hm with ⟨j, hj, hf⟩
  have h := Equiv.natSumNatEquivNat.injective (he.trans hf.symm)
  cases h

theorem countableJoinList_mem_env (j : ℕ) (A B : Finset ℕ) :
    Equiv.natSumNatEquivNat (Sum.inl j) ∈ countableJoinList A B ↔ j ∈ A := by
  simp only [countableJoinList, List.mem_append, List.mem_map, Equiv.apply_eq_iff_eq,
    Equiv.symm_apply_apply, Sum.inl.injEq, Sum.inr_ne_inl, and_false, exists_false,
    or_false, exists_eq_right, Finset.mem_sort]

theorem countableJoinList_mem_sys (j : ℕ) (A B : Finset ℕ) :
    Equiv.natSumNatEquivNat (Sum.inr j) ∈ countableJoinList A B ↔ j ∈ B := by
  simp only [countableJoinList, List.mem_append, List.mem_map, Equiv.apply_eq_iff_eq,
    Equiv.symm_apply_apply, Sum.inr.injEq, Sum.inl_ne_inr, and_false, exists_false,
    false_or, exists_eq_right, Finset.mem_sort]

theorem countableJoinList_toFinset (A B : Finset ℕ) :
    (countableJoinList A B).toFinset = countableSplitIndex (A,B) := by
  ext n
  rcases Equiv.natSumNatEquivNat.surjective n with ⟨j,rfl⟩
  cases j with
  | inl j => simp only [List.mem_toFinset, countableJoinList_mem_env, countableSplitIndex_mem_env]
  | inr j => simp only [List.mem_toFinset, countableJoinList_mem_sys, countableSplitIndex_mem_sys]

def countableJoinImage (AB : Finset ℕ × Finset ℕ) : CountableSpace :=
  countableWord orbitalKet (countableJoinList AB.1 AB.2)

theorem countableJoinImage_ket (A B : Finset ℕ) :
    countableJoinImage (A,B) = countableWordSign (countableJoinList A B) •
      countableKet (countableSplitIndex (A,B)) := by
  rw [countableJoinImage, countableWord_ket _ (countableJoinList_nodup A B),
    countableJoinList_toFinset]

theorem countableJoinImage_sector (A B : Finset ℕ) :
    countableJoinImage (A,B) ∈ countableSector (A.card + B.card) := by
  simpa only [countableJoinImage, countableJoinList_length] using
    countableWord_sector orbitalKet (countableJoinList A B)

theorem countableJoinImage_norm (AB : Finset ℕ × Finset ℕ) :
    ‖countableJoinImage AB‖ = 1 := by
  rw [countableJoinImage_ket, norm_smul, countableWordSign_norm, countableKet_norm, one_mul]

end VortexGap.Fermion
