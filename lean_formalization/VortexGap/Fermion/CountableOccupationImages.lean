import VortexGap.Fermion.CountableWords

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped InnerProduct

/-- A finite occupation mapped to its actual ascending creation word. -/
def countableOccupationImage (v : ℕ → CountableOrbital) (A : Finset ℕ) : CountableSpace :=
  countableWord v (A.sort (· ≤ ·))

theorem countableOccupationImage_empty (v : ℕ → CountableOrbital) :
    countableOccupationImage v ∅ = countableKet ∅ := by
  simp only [countableOccupationImage, Finset.sort_empty, countableWord_nil]

theorem countableOccupationImage_singleton (v : ℕ → CountableOrbital) (j : ℕ) :
    countableOccupationImage v {j} = countableCreate (v j) (countableKet ∅) := by
  simp only [countableOccupationImage, Finset.sort_singleton, countableWord_cons, countableWord_nil]

theorem countableOccupationImage_sector (v : ℕ → CountableOrbital) (A : Finset ℕ) :
    countableOccupationImage v A ∈ countableSector A.card := by
  simpa only [countableOccupationImage, Finset.length_sort] using
    countableWord_sector v (A.sort (· ≤ ·))

theorem countableOccupationImage_norm (v : ℕ → CountableOrbital) (hv : Orthonormal ℂ v)
    (A : Finset ℕ) : ‖countableOccupationImage v A‖ = 1 :=
  countableWord_norm v hv _ (Finset.sort_nodup A (· ≤ ·))

theorem countableOccupationImage_inner (v : ℕ → CountableOrbital) (hv : Orthonormal ℂ v)
    (A B : Finset ℕ) :
    inner ℂ (countableOccupationImage v A) (countableOccupationImage v B) =
      if A = B then 1 else 0 := by
  by_cases he : A = B
  · subst B
    rw [ite_eq_left rfl]
    exact countableWord_inner_self v hv _ (Finset.sort_nodup A (· ≤ ·))
  · rw [ite_eq_right he]
    by_cases ha : ∃ j ∈ A, j ∉ B
    · obtain ⟨j, hj, hk⟩ := ha
      exact countableWord_inner_zero_of_mem v hv _ _ (Finset.sort_nodup A (· ≤ ·)) j
        ((Finset.mem_sort (· ≤ ·)).mpr hj) (by simpa only [Finset.mem_sort] using hk)
    · have hb : ∃ j ∈ B, j ∉ A := by
        by_contra hb
        push Not at hb
        apply he
        ext j
        constructor
        · intro hj
          by_contra hn
          exact ha ⟨j, hj, hn⟩
        · exact hb j
      obtain ⟨j, hj, hk⟩ := hb
      have hz := countableWord_inner_zero_of_mem v hv (B.sort (· ≤ ·)) (A.sort (· ≤ ·)) (Finset.sort_nodup B (· ≤ ·)) j
        ((Finset.mem_sort (· ≤ ·)).mpr hj) (by simpa only [Finset.mem_sort] using hk)
      rw [← inner_conj_symm]
      change (starRingEnd ℂ) (inner ℂ (countableWord v (B.sort (· ≤ ·)))
        (countableWord v (A.sort (· ≤ ·)))) = 0
      rw [hz, map_zero]

theorem countableOccupationImage_orthonormal (v : ℕ → CountableOrbital)
    (hv : Orthonormal ℂ v) : Orthonormal ℂ (countableOccupationImage v) :=
  orthonormal_iff_ite.mpr (countableOccupationImage_inner v hv)

theorem countableOccupationImage_insert_min (v : ℕ → CountableOrbital)
    (j : ℕ) (A : Finset ℕ) (hj : j ∉ A) (hmin : ∀ k ∈ A, j ≤ k) :
    countableOccupationImage v (insert j A) =
      countableCreate (v j) (countableOccupationImage v A) := by
  rw [countableOccupationImage, Finset.sort_insert (· ≤ ·) hmin hj]
  rfl

theorem countableSign_of_forall_ge (j : ℕ) (A : Finset ℕ) (hmin : ∀ k ∈ A, j ≤ k) :
    countableSign j A = 1 := by
  have hf : A.filter (· < j) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro k hk
    obtain ⟨hkA, hkj⟩ := Finset.mem_filter.mp hk
    exact (not_lt_of_ge (hmin k hkA)) hkj
  simp only [countableSign, hf, Finset.card_empty, pow_zero]

theorem countableOccupationImage_orbitalKet (A : Finset ℕ) :
    countableOccupationImage orbitalKet A = countableKet A := by
  induction A using Finset.induction_on_min with
  | empty => exact countableOccupationImage_empty _
  | insert j A hmin ih =>
      have hj : j ∉ A := fun h => (lt_irrefl j) (hmin j h)
      have hle : ∀ k ∈ A, j ≤ k := fun k hk => (hmin k hk).le
      rw [countableOccupationImage_insert_min _ j A hj hle, countableCreate_ket, ih,
        countableCreateMode_ket j A hj, countableSign_of_forall_ge j A hle, one_smul]

theorem orbitalKet_orthonormal : Orthonormal ℂ orbitalKet := by
  apply orthonormal_iff_ite.mpr
  intro i j
  rw [orbitalKet_inner_left]
  simp only [orbitalKet, lp.single_apply]
  split_ifs <;> simp_all

end VortexGap.Fermion
