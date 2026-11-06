import VortexGap.Fermion.CountableWordOperators

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion

def countableOccupationOperator (v : ℕ → CountableOrbital) (A : Finset ℕ) :
    CountableSpace →L[ℂ] CountableSpace := countableWordOperator v (A.sort (· ≤ ·))

theorem countableOccupationOperator_empty (v : ℕ → CountableOrbital) (x : CountableSpace) :
    countableOccupationOperator v ∅ x = x := by
  simp only [countableOccupationOperator, Finset.sort_empty, countableWordOperator_nil]

theorem countableOccupationOperator_singleton (v : ℕ → CountableOrbital) (j : ℕ)
    (x : CountableSpace) :
    countableOccupationOperator v {j} x = countableCreate (v j) x := by
  simp only [countableOccupationOperator, Finset.sort_singleton, countableWordOperator_cons,
    countableWordOperator_nil]

theorem countableOccupationOperator_vacuum (v : ℕ → CountableOrbital) (A : Finset ℕ) :
    countableOccupationOperator v A (countableKet ∅) = countableOccupationImage v A :=
  countableWordOperator_vacuum v (A.sort (· ≤ ·))

theorem countableOccupationOperator_insert_min (v : ℕ → CountableOrbital)
    (j : ℕ) (A : Finset ℕ) (hj : j ∉ A) (hmin : ∀ k ∈ A, j ≤ k) (x : CountableSpace) :
    countableOccupationOperator v (insert j A) x =
      countableCreate (v j) (countableOccupationOperator v A x) := by
  rw [countableOccupationOperator, Finset.sort_insert (· ≤ ·) hmin hj]
  rfl

theorem countableWordOperator_create_of_mem (v : ℕ → CountableOrbital) (j : ℕ)
    (js : List ℕ) (hj : j ∈ js) (x : CountableSpace) :
    countableCreate (v j) (countableWordOperator v js x) = 0 := by
  induction js with
  | nil => simp at hj
  | cons k ks ih =>
      rcases List.mem_cons.mp hj with he | hmem
      · subst k
        exact congrArg (fun T : CountableSpace →L[ℂ] CountableSpace =>
          T (countableWordOperator v ks x)) (countableCreate_square (v j))
      · have h := congrArg (fun T : CountableSpace →L[ℂ] CountableSpace =>
          T (countableWordOperator v ks x)) (countableCreate_anticommute (v j) (v k))
        change countableCreate (v j) (countableCreate (v k) _) =
          -(countableCreate (v k) (countableCreate (v j) _)) at h
        rw [countableWordOperator_cons, h, ih hmem, map_zero, neg_zero]

theorem countableOccupationOperator_create_of_mem (v : ℕ → CountableOrbital)
    (j : ℕ) (A : Finset ℕ) (hj : j ∈ A) (x : CountableSpace) :
    countableCreate (v j) (countableOccupationOperator v A x) = 0 :=
  countableWordOperator_create_of_mem v j _ ((Finset.mem_sort (· ≤ ·)).mpr hj) x

/-- The insertion identity is an identity of bounded creation words, not just vacuum vectors. -/
theorem countableOccupationOperator_create_of_not_mem (v : ℕ → CountableOrbital)
    (j : ℕ) (A : Finset ℕ) (hj : j ∉ A) (x : CountableSpace) :
    countableCreate (v j) (countableOccupationOperator v A x) =
      countableSign j A • countableOccupationOperator v (insert j A) x := by
  induction A using Finset.induction_on_min generalizing j with
  | empty =>
      rw [countableOccupationOperator_empty, Finset.insert_empty, countableOccupationOperator_singleton]
      simp only [countableSign, Finset.filter_empty, Finset.card_empty, pow_zero, one_smul]
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
        rw [countableSign_of_forall_ge j (insert k A) hminj, one_smul,
          countableOccupationOperator_insert_min v j (insert k A) hj hminj]
      · have hkj : k < j := by omega
        have hknew : k ∉ insert j A := by simp only [Finset.mem_insert]; tauto
        have hminnew : ∀ a ∈ insert j A, k ≤ a := by
          intro a ha
          rcases Finset.mem_insert.mp ha with rfl | ha
          · exact hkj.le
          · exact hle a ha
        have hanti := congrArg (fun T : CountableSpace →L[ℂ] CountableSpace =>
          T (countableOccupationOperator v A x)) (countableCreate_anticommute (v j) (v k))
        change countableCreate (v j) (countableCreate (v k) _) =
          -(countableCreate (v k) (countableCreate (v j) _)) at hanti
        rw [countableOccupationOperator_insert_min v k A hk hle, hanti, ih j hjA, map_smul,
          Finset.insert_comm j k A,
          countableOccupationOperator_insert_min v k (insert j A) hknew hminnew,
          countableSign_insert j hk, ite_eq_left hkj, neg_smul]

theorem countableOccupationOperator_create (v : ℕ → CountableOrbital) (A : Finset ℕ)
    (w : CountableOrbital) (x : CountableSpace) :
    countableCreate w (countableOccupationOperator v A x) =
      (-1 : ℂ) ^ A.card • countableOccupationOperator v A (countableCreate w x) := by
  simpa only [countableOccupationOperator, Finset.length_sort] using
    countableWordOperator_create v (A.sort (· ≤ ·)) w x

end VortexGap.Fermion
