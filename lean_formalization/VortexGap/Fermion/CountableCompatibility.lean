import VortexGap.Fermion.CountableCAR
import VortexGap.Fermion.CountableSectors

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion

/-- Every finite occupation operator is the restriction of the concrete countable one. -/
theorem countableTransition_embed {n : ℕ} (j : Fin n) (ε : Bool) (x : Space n) :
    countableTransition j.val ε (countableEmbed n x) =
      countableEmbed n (OAI.LaughlinGap.Occupation.transition j ε x) := by
  have hc (y : Space n) (A : Finset (Fin n)) : countableEmbed n y (occupationIndex A) = y A :=
    countableEmbedLinear_coefficient y A
  ext B
  by_cases hB : B ⊆ Finset.range n
  · obtain ⟨A, rfl⟩ := occupationIndex_exists B hB
    simp only [countableTransition_apply, occupationIndex_mem, occupationIndex_sign,
      occupationIndex_flip, hc, OAI.LaughlinGap.Occupation.transition_apply]
  · have hf : ¬ countableFlip j.val B ⊆ Finset.range n := by
      intro h
      apply hB
      intro k hk
      by_cases hkj : k = j.val
      · subst k; exact Finset.mem_range.mpr j.isLt
      · exact h ((countableFlip_mem_other hkj B).mpr hk)
    rw [countableEmbed_outside _ B hB, countableTransition_apply,
      countableEmbed_outside x _ hf]
    split_ifs <;> simp

theorem countableRestrict_transition {n : ℕ} (j : Fin n) (ε : Bool) (x : CountableSpace) :
    countableRestrict n (countableTransition j.val ε x) =
      OAI.LaughlinGap.Occupation.transition j ε (countableRestrict n x) := by
  ext A
  simp only [countableRestrict_coefficient, countableTransition_apply,
    occupationIndex_mem, occupationIndex_sign, occupationIndex_flip,
    OAI.LaughlinGap.Occupation.transition_apply]

/-- A cutoff commutes with modes it contains, for both creation and annihilation. -/
theorem countableTransition_cutoff {n : ℕ} (j : Fin n) (ε : Bool) (x : CountableSpace) :
    countableTransition j.val ε (countableCutoff n x) =
      countableCutoff n (countableTransition j.val ε x) := by
  calc
    _ = countableTransition j.val ε (countableEmbed n (countableRestrict n x)) :=
      congrArg (countableTransition j.val ε) (countableEmbed_restrict n x).symm
    _ = countableEmbed n (OAI.LaughlinGap.Occupation.transition j ε (countableRestrict n x)) :=
      countableTransition_embed j ε _
    _ = countableEmbed n (countableRestrict n (countableTransition j.val ε x)) :=
      congrArg (countableEmbed n) (countableRestrict_transition j ε x).symm
    _ = _ := countableEmbed_restrict n _

theorem countableAnnihilateMode_sector {N : ℕ} (j : ℕ) {x : CountableSpace}
    (hx : x ∈ countableSector (N + 1)) : countableAnnihilateMode j x ∈ countableSector N := by
  intro A hA
  by_cases hj : j ∈ A
  · simp [countableAnnihilateMode, countableTransition_apply, hj]
  · have hc : (insert j A).card ≠ N + 1 := by
      rw [Finset.card_insert_of_notMem hj]
      omega
    simp [countableAnnihilateMode, countableTransition_apply, hj, hx _ hc]

theorem countableCreateMode_sector {N : ℕ} (j : ℕ) {x : CountableSpace}
    (hx : x ∈ countableSector N) : countableCreateMode j x ∈ countableSector (N + 1) := by
  intro A hA
  by_cases hj : j ∈ A
  · have hc : (A.erase j).card ≠ N := by
      have := Finset.card_erase_add_one hj
      omega
    simp [countableCreateMode, countableTransition_apply, hj, hx _ hc]
  · simp [countableCreateMode, countableTransition_apply, hj]

theorem countableAnnihilateMode_zero_sector (j : ℕ) {x : CountableSpace}
    (hx : x ∈ countableSector 0) : countableAnnihilateMode j x = 0 := by
  ext A
  by_cases hj : j ∈ A
  · simp [countableAnnihilateMode, countableTransition_apply, hj]
  · have hc : (insert j A).card ≠ 0 := by rw [Finset.card_insert_of_notMem hj]; omega
    simp [countableAnnihilateMode, countableTransition_apply, hj, hx _ hc]

end VortexGap.Fermion

