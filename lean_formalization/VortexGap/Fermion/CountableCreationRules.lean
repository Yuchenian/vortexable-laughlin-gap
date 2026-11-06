import VortexGap.Fermion.CountableOccupationImages

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped InnerProduct

theorem countableCreate_word_of_mem (v : ℕ → CountableOrbital) (j : ℕ)
    (js : List ℕ) (hj : j ∈ js) :
    countableCreate (v j) (countableWord v js) = 0 := by
  induction js with
  | nil => simp at hj
  | cons k ks ih =>
      rcases List.mem_cons.mp hj with he | hmem
      · subst k
        have h := congrArg (fun T : CountableSpace →L[ℂ] CountableSpace =>
          T (countableWord v ks)) (countableCreate_square (v j))
        exact h
      · have h := congrArg (fun T : CountableSpace →L[ℂ] CountableSpace =>
          T (countableWord v ks)) (countableCreate_anticommute (v j) (v k))
        change countableCreate (v j) (countableCreate (v k) (countableWord v ks)) =
          -(countableCreate (v k) (countableCreate (v j) (countableWord v ks))) at h
        rw [countableWord_cons, h, ih hmem, map_zero, neg_zero]

theorem countableCreate_image_of_mem (v : ℕ → CountableOrbital) (j : ℕ)
    (A : Finset ℕ) (hj : j ∈ A) :
    countableCreate (v j) (countableOccupationImage v A) = 0 :=
  countableCreate_word_of_mem v j _ ((Finset.mem_sort (· ≤ ·)).mpr hj)

/-- The insertion sign is proved for arbitrary orbitals, not assumed from an exterior functor. -/
theorem countableCreate_image_of_not_mem (v : ℕ → CountableOrbital) (j : ℕ)
    (A : Finset ℕ) (hj : j ∉ A) :
    countableCreate (v j) (countableOccupationImage v A) =
      countableSign j A • countableOccupationImage v (insert j A) := by
  induction A using Finset.induction_on_min generalizing j with
  | empty =>
      rw [countableOccupationImage_empty, Finset.insert_empty, countableOccupationImage_singleton]
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
          countableOccupationImage_insert_min v j (insert k A) hj hminj]
      · have hkj : k < j := by omega
        have hknew : k ∉ insert j A := by simp only [Finset.mem_insert]; tauto
        have hminnew : ∀ a ∈ insert j A, k ≤ a := by
          intro a ha
          rcases Finset.mem_insert.mp ha with rfl | ha
          · exact hkj.le
          · exact hle a ha
        have hanti := congrArg (fun T : CountableSpace →L[ℂ] CountableSpace =>
          T (countableOccupationImage v A)) (countableCreate_anticommute (v j) (v k))
        change countableCreate (v j) (countableCreate (v k) (countableOccupationImage v A)) =
          -(countableCreate (v k) (countableCreate (v j) (countableOccupationImage v A))) at hanti
        rw [countableOccupationImage_insert_min v k A hk hle, hanti, ih j hjA, map_smul,
          Finset.insert_comm j k A,
          countableOccupationImage_insert_min v k (insert j A) hknew hminnew,
          countableSign_insert j hk, ite_eq_left hkj, neg_smul]

theorem countableAnnihilate_image_of_not_mem (v : ℕ → CountableOrbital)
    (hv : Orthonormal ℂ v) (j : ℕ) (A : Finset ℕ) (hj : j ∉ A) :
    countableAnnihilate (v j) (countableOccupationImage v A) = 0 :=
  countableAnnihilate_word_of_not_mem v hv j _
    (by simpa only [Finset.mem_sort] using hj)

theorem countableAnnihilate_image_of_mem (v : ℕ → CountableOrbital)
    (hv : Orthonormal ℂ v) (j : ℕ) (A : Finset ℕ) (hj : j ∈ A) :
    countableAnnihilate (v j) (countableOccupationImage v A) =
      countableSign j A • countableOccupationImage v (A.erase j) := by
  have hs : countableSign j (A.erase j) = countableSign j A := by
    simpa only [countableFlip_of_mem hj] using countableSign_flip_self j A
  have hc := countableCreate_image_of_not_mem v j (A.erase j) (Finset.notMem_erase j A)
  rw [Finset.insert_erase hj, hs] at hc
  have ha := congrArg (countableAnnihilate (v j)) hc
  rw [countableAnnihilate_create, (orthonormal_iff_ite.mp hv) j j, ite_eq_left rfl,
    one_smul, countableAnnihilate_image_of_not_mem v hv j (A.erase j) (Finset.notMem_erase j A),
    map_zero, sub_zero, map_smul] at ha
  calc
    _ = countableSign j A • (countableSign j A •
        countableAnnihilate (v j) (countableOccupationImage v A)) := by
      rw [smul_smul, countableSign_sq, one_smul]
    _ = _ := by rw [← ha]

end VortexGap.Fermion
