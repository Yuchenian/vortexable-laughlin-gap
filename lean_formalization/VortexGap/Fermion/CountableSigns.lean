import VortexGap.Fermion.CountableApproximation

/-! Natural-label occupation algebra. The flip/sign arguments adapt the pinned
OAI.Analysis.LaughlinGap.Occupation construction (Apache-2.0; vendored source and
license in vendor/upstream_audit). The finite-index compatibility is proved below. -/
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion

def countableFlip (j : ℕ) : Equiv.Perm (Finset ℕ) :=
  let f : Finset ℕ → Finset ℕ := fun A => if j ∈ A then A.erase j else insert j A
  have h : Function.Involutive f := by
    intro A
    by_cases hj : j ∈ A <;> simp [f, hj]
  ⟨f, f, h, h⟩

@[simp]
theorem countableFlip_of_mem {j : ℕ} {A : Finset ℕ} (h : j ∈ A) :
    countableFlip j A = A.erase j := ite_eq_left h

@[simp]
theorem countableFlip_of_not_mem {j : ℕ} {A : Finset ℕ} (h : j ∉ A) :
    countableFlip j A = insert j A := ite_eq_right h

@[simp]
theorem countableFlip_flip (j : ℕ) (A : Finset ℕ) :
    countableFlip j (countableFlip j A) = A := (countableFlip j).left_inv A

@[simp]
theorem countableFlip_mem_self (j : ℕ) (A : Finset ℕ) :
    j ∈ countableFlip j A ↔ j ∉ A := by
  by_cases h : j ∈ A <;> simp [h]

@[simp]
theorem countableFlip_mem_other {i j : ℕ} (h : i ≠ j) (A : Finset ℕ) :
    i ∈ countableFlip j A ↔ i ∈ A := by
  by_cases hj : j ∈ A <;> simp [hj, h]

theorem countableFlip_comm (i j : ℕ) (A : Finset ℕ) :
    countableFlip i (countableFlip j A) = countableFlip j (countableFlip i A) := by
  by_cases hij : i = j
  · subst j; rfl
  ext k
  by_cases hki : k = i
  · subst k; simp [hij]
  by_cases hkj : k = j
  · subst k; simp [Ne.symm hij]
  simp [hki, hkj]

def countableSign (j : ℕ) (A : Finset ℕ) : ℂ :=
  (-1 : ℂ) ^ (A.filter (fun k => k < j)).card

@[simp]
theorem countableSign_norm (j : ℕ) (A : Finset ℕ) : ‖countableSign j A‖ = 1 := by
  simp [countableSign, norm_pow]

@[simp]
theorem countableSign_conj (j : ℕ) (A : Finset ℕ) :
    starRingEnd ℂ (countableSign j A) = countableSign j A := by
  simp only [countableSign, map_pow, map_neg, map_one]

@[simp]
theorem countableSign_sq (j : ℕ) (A : Finset ℕ) :
    countableSign j A * countableSign j A = 1 := by
  unfold countableSign
  rw [← mul_pow]
  norm_num

theorem countableSign_insert (j : ℕ) {i : ℕ} {A : Finset ℕ} (hi : i ∉ A) :
    countableSign j (insert i A) = if i < j then -countableSign j A else countableSign j A := by
  by_cases hij : i < j
  · simp [countableSign, Finset.filter_insert, hij, Finset.card_insert_of_notMem, hi, pow_succ]
  · simp [countableSign, Finset.filter_insert, hij]

theorem countableSign_flip (i j : ℕ) (A : Finset ℕ) :
    countableSign j (countableFlip i A) =
      if i < j then -countableSign j A else countableSign j A := by
  by_cases hi : i ∈ A
  · have h := countableSign_insert j (Finset.notMem_erase i A)
    rw [Finset.insert_erase hi] at h
    rw [countableFlip_of_mem hi]
    split_ifs with hij
    · simp only [ite_eq_left hij] at h
      rw [h, neg_neg]
    · simpa [hij] using h.symm
  · rw [countableFlip_of_not_mem hi, countableSign_insert j hi]

@[simp]
theorem countableSign_flip_self (j : ℕ) (A : Finset ℕ) :
    countableSign j (countableFlip j A) = countableSign j A := by
  simp [countableSign_flip]

theorem occupationIndex_mem {n : ℕ} (j : Fin n) (A : Finset (Fin n)) :
    j.val ∈ occupationIndex A ↔ j ∈ A := by simp [occupationIndex]

theorem occupationIndex_flip {n : ℕ} (j : Fin n) (A : Finset (Fin n)) :
    countableFlip j.val (occupationIndex A) =
      occupationIndex (OAI.LaughlinGap.Occupation.flip j A) := by
  by_cases h : j ∈ A
  · rw [countableFlip_of_mem ((occupationIndex_mem j A).mpr h),
      OAI.LaughlinGap.Occupation.flip_of_mem h]
    exact (Finset.map_erase ⟨Fin.val, Fin.val_injective⟩ A j).symm
  · rw [countableFlip_of_not_mem (by simpa only [occupationIndex_mem] using h),
      OAI.LaughlinGap.Occupation.flip_of_not_mem h]
    exact (Finset.map_insert ⟨Fin.val, Fin.val_injective⟩ j A).symm

theorem occupationIndex_sign {n : ℕ} (j : Fin n) (A : Finset (Fin n)) :
    countableSign j.val (occupationIndex A) = OAI.LaughlinGap.Occupation.sign j A := by
  unfold countableSign OAI.LaughlinGap.Occupation.sign occupationIndex
  rw [Finset.filter_map, Finset.card_map]
  rfl

end VortexGap.Fermion

