import VortexGap.Reference.Coordinates
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped BigOperators

theorem upstreamOccupation_sorted (L : ℕ) (A : Finset (Fin (L+1))) :
    OAI.Laughlin.Fock.occupationBasis L A =
      ((A.sort (· ≤ ·)).map (fun i => ExteriorAlgebra.ι ℂ (OAI.Laughlin.Fock.mode i))).prod := by
  change (Pi.basisFun ℂ (Fin (L+1))).ExteriorAlgebra A = _
  rw [ExteriorAlgebra.basis_apply]
  change (List.ofFn (fun i : Fin A.card => ExteriorAlgebra.ι ℂ
    ((Pi.basisFun ℂ (Fin (L+1))) (A.orderEmbOfFin rfl i)))).prod = _
  rw [List.ofFn_eq_map]
  change ((List.finRange A.card).map
    ((fun i => ExteriorAlgebra.ι ℂ ((Pi.basisFun ℂ (Fin (L+1))) i)) ∘ A.orderEmbOfFin rfl)).prod = _
  rw [← List.map_map, Finset.listMap_orderEmbOfFin_finRange]
  simp [Pi.basisFun_apply, OAI.Laughlin.Fock.mode]

theorem upstreamOccupation_insert_min (L : ℕ) (i : Fin (L+1))
    (A : Finset (Fin (L+1))) (hi : i ∉ A) (hmin : ∀ j ∈ A, i ≤ j) :
    OAI.Laughlin.Fock.occupationBasis L (insert i A) =
      OAI.Laughlin.Fock.create i (OAI.Laughlin.Fock.occupationBasis L A) := by
  rw [upstreamOccupation_sorted, Finset.sort_insert (· ≤ ·) hmin hi,
    List.map_cons, List.prod_cons, ← upstreamOccupation_sorted]
  rfl

open OAI.LaughlinGap.Occupation

theorem upstreamCreate_parity (L : ℕ) (j : Fin (L+1)) (A : Finset (Fin (L+1)))
    (hj : j ∉ A) :
    OAI.Laughlin.Fock.create j (OAI.Laughlin.Fock.occupationBasis L A) =
      sign j A • OAI.Laughlin.Fock.occupationBasis L (insert j A) := by
  have hsignmin (j : Fin (L+1)) (B : Finset (Fin (L+1)))
      (hmin : ∀ k ∈ B, j ≤ k) : sign j B = 1 := by
    have hf : B.filter (· < j) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro k hk
      obtain ⟨hkB, hkj⟩ := Finset.mem_filter.mp hk
      exact (not_lt_of_ge (hmin k hkB)) hkj
    simp [sign, hf]
  induction A using Finset.induction_on_min generalizing j with
  | empty =>
      rw [upstreamOccupation_insert_min L j ∅ (by simp) (by simp)]
      simp [sign]
  | insert k A hmin ih =>
      have hk : k ∉ A := fun h => (lt_irrefl k) (hmin k h)
      have hjA : j ∉ A := fun h => hj (Finset.mem_insert_of_mem h)
      have hjk : j ≠ k := fun h => hj (by simp [h])
      have hle : ∀ a ∈ A, k ≤ a := fun a ha => (hmin a ha).le
      by_cases hfront : j < k
      · have hminj : ∀ a ∈ insert k A, j ≤ a := by
          intro a ha
          rcases Finset.mem_insert.mp ha with rfl | ha
          · exact hfront.le
          · exact hfront.le.trans (hle a ha)
        rw [hsignmin j (insert k A) hminj, one_smul,
          upstreamOccupation_insert_min L j (insert k A) hj hminj]
      · have hkj : k < j := lt_of_le_of_ne (le_of_not_gt hfront) (Ne.symm hjk)
        have hknew : k ∉ insert j A := by simp only [Finset.mem_insert]; tauto
        have hminnew : ∀ a ∈ insert j A, k ≤ a := by
          intro a ha
          rcases Finset.mem_insert.mp ha with rfl | ha
          · exact hkj.le
          · exact hle a ha
        have hanti := LinearMap.congr_fun (OAI.Laughlin.Fock.create_anticommute j k)
          (OAI.Laughlin.Fock.occupationBasis L A)
        change OAI.Laughlin.Fock.create j (OAI.Laughlin.Fock.create k
          (OAI.Laughlin.Fock.occupationBasis L A)) +
          OAI.Laughlin.Fock.create k (OAI.Laughlin.Fock.create j
          (OAI.Laughlin.Fock.occupationBasis L A)) = 0 at hanti
        have he := eq_neg_of_add_eq_zero_left hanti
        rw [upstreamOccupation_insert_min L k A hk hle, he, ih j hjA, map_smul,
          Finset.insert_comm j k A,
          upstreamOccupation_insert_min L k (insert j A) hknew hminnew,
          sign_insert j hk, ite_eq_left hkj, neg_smul]

theorem upstreamInsertionSign_eq (L : ℕ) (i : Fin (L+1))
    (A : Finset (Fin (L+1))) (hi : i ∉ A) :
    OAI.Laughlin.Fock.insertionSign L i A = sign i A := by
  have h := (OAI.Laughlin.Fock.create_unoccupied L i A hi).symm.trans
    (upstreamCreate_parity L i A hi)
  have hc := congrArg (fun x => (OAI.Laughlin.Fock.occupationBasis L).repr x (insert i A)) h
  simpa using hc

theorem upstreamCoordinates_annihilate (L : ℕ) (i : Fin (L+1))
    (x : OAI.Laughlin.Fock.Space L) :
    upstreamCoordinates L (OAI.Laughlin.Fock.annihilate i x) =
      annihilateMode i (upstreamCoordinates L x) := by
  ext A
  rw [upstreamCoordinates_apply, OAI.Laughlin.Fock.annihilate_coordinate]
  by_cases hi : i ∈ A
  · simp [annihilateMode, annihilation, transition_apply, hi]
  · simp [annihilateMode, annihilation, transition_apply, hi,
      upstreamInsertionSign_eq L i A hi, upstreamCoordinates_apply]


theorem upstreamCoordinates_create (L : ℕ) (i : Fin (L+1))
    (x : OAI.Laughlin.Fock.Space L) :
    upstreamCoordinates L (OAI.Laughlin.Fock.create i x) =
      createMode i (upstreamCoordinates L x) := by
  ext A
  rw [upstreamCoordinates_apply, OAI.Laughlin.Fock.create_coordinate]
  by_cases hi : i ∈ A
  · simp [createMode, creation, transition_apply, hi,
      upstreamInsertionSign_eq L i (A.erase i) (Finset.notMem_erase i A),
      upstreamCoordinates_apply]
  · simp [createMode, creation, transition_apply, hi]

end VortexGap.Fermion
