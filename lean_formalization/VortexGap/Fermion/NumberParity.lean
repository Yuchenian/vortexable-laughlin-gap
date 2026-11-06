import VortexGap.Fermion.Pair

/-! Actual occupation-number grading and parity on full finite-mode Fock space. -/
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped BigOperators InnerProduct
open OAI.LaughlinGap.Occupation

def number (n : ℕ) : Module.End ℂ (Space n) where
  toFun x := WithLp.toLp 2 (fun A => (A.card : ℂ) * x A)
  map_add' x y := by ext A; simp [mul_add]
  map_smul' z x := by ext A; simp [mul_left_comm]

def parity (n : ℕ) : Module.End ℂ (Space n) where
  toFun x := WithLp.toLp 2 (fun A => (-1 : ℂ)^A.card * x A)
  map_add' x y := by ext A; simp [mul_add]
  map_smul' z x := by ext A; simp [mul_left_comm]

theorem number_apply {n : ℕ} (x : Space n) (A : Finset (Fin n)) :
    number n x A = (A.card : ℂ) * x A := rfl

theorem parity_apply {n : ℕ} (x : Space n) (A : Finset (Fin n)) :
    parity n x A = (-1 : ℂ)^A.card * x A := rfl

theorem occupationMode_apply {n : ℕ} (i : Fin n) (x : Space n) (A : Finset (Fin n)) :
    (createMode i * annihilateMode i) x A = if i ∈ A then x A else 0 := by
  by_cases hi : i ∈ A <;>
    simp [Module.End.mul_apply, createMode, annihilateMode, creation, annihilation,
      transition_apply, hi, ← mul_assoc]

theorem number_eq_sum {n : ℕ} :
    number n = ∑ i : Fin n, createMode i * annihilateMode i := by
  ext x A
  simp only [number_apply, LinearMap.sum_apply, WithLp.ofLp_sum, Finset.sum_apply,
    occupationMode_apply]
  simp [Finset.sum_ite_mem]

theorem parity_square {n : ℕ} : parity n * parity n = 1 := by
  ext x A
  change (-1 : ℂ)^A.card * ((-1 : ℂ)^A.card * x A) = x A
  rw [← mul_assoc, ← mul_pow]
  simp

theorem parity_vacuum {n : ℕ} : parity n (ket ∅) = ket ∅ := by
  ext A
  by_cases h : A = ∅ <;> simp [parity_apply, ket, h]

theorem parity_annihilateMode {n : ℕ} (i : Fin n) :
    parity n * annihilateMode i = -(annihilateMode i * parity n) := by
  ext x A
  change (-1 : ℂ)^A.card * annihilation i x A = -annihilation i (parity n x) A
  by_cases hi : i ∈ A
  · simp [transition_apply, hi]
  · simp [transition_apply, hi, parity_apply, Finset.card_insert_of_notMem, pow_succ]
    ring

theorem parity_createMode {n : ℕ} (i : Fin n) :
    parity n * createMode i = -(createMode i * parity n) := by
  ext x A
  change (-1 : ℂ)^A.card * creation i x A = -creation i (parity n x) A
  by_cases hi : i ∈ A
  · have hc := Finset.card_erase_add_one hi
    simp only [transition_apply, hi, decide_true, ite_true, flip_of_mem hi, parity_apply]
    rw [← hc, pow_succ]
    ring
  · simp [transition_apply, hi]

theorem parity_pairMode {n : ℕ} (a : PairIndex n) :
    parity n * pairMode a = pairMode a * parity n := by
  simp only [pairMode, ← mul_assoc, parity_annihilateMode, neg_mul]
  rw [mul_assoc, parity_annihilateMode]
  simp [mul_assoc]

/-- Support on exactly N particles; there is no truncation of creation operators. -/
def InSector {n : ℕ} (N : ℕ) (x : Space n) : Prop :=
  ∀ A, A.card ≠ N → x A = 0

theorem sector_zero {n N : ℕ} : InSector N (0 : Space n) := by intro A _; rfl

theorem sector_add {n N : ℕ} {x y : Space n} (hx : InSector N x) (hy : InSector N y) :
    InSector N (x + y) := by intro A hA; simp [hx A hA, hy A hA]

theorem sector_smul {n N : ℕ} (z : ℂ) {x : Space n} (hx : InSector N x) :
    InSector N (z • x) := by intro A hA; simp [hx A hA]

theorem sector_sum {n N : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Space n)
    (hf : ∀ i ∈ s, InSector N (f i)) : InSector N (∑ i ∈ s, f i) := by
  intro A hA
  simp only [WithLp.ofLp_sum, Finset.sum_apply]
  exact Finset.sum_eq_zero fun i hi => hf i hi A hA

theorem sector_ket {n : ℕ} (A : Finset (Fin n)) : InSector A.card (ket A) := by
  intro B hB
  have h : A ≠ B := by intro e; subst B; exact hB rfl
  simp [ket, h]

theorem number_on_sector {n N : ℕ} {x : Space n} (hx : InSector N x) :
    number n x = (N : ℂ) • x := by
  ext A
  by_cases hA : A.card = N <;> simp [number_apply, hA, hx A]

theorem parity_on_sector {n N : ℕ} {x : Space n} (hx : InSector N x) :
    parity n x = (-1 : ℂ)^N • x := by
  ext A
  by_cases hA : A.card = N <;> simp [parity_apply, hA, hx A]

theorem annihilateMode_sector {n N : ℕ} (i : Fin n) {x : Space n}
    (hx : InSector (N + 1) x) : InSector N (annihilateMode i x) := by
  intro A hA
  by_cases hi : i ∈ A
  · simp [annihilateMode, annihilation, transition_apply, hi]
  · have hc : (insert i A).card ≠ N + 1 := by
      rw [Finset.card_insert_of_notMem hi]
      omega
    simp [annihilateMode, annihilation, transition_apply, hi, hx _ hc]

theorem createMode_sector {n N : ℕ} (i : Fin n) {x : Space n}
    (hx : InSector N x) : InSector (N + 1) (createMode i x) := by
  intro A hA
  by_cases hi : i ∈ A
  · have hc : (A.erase i).card ≠ N := by
      have := Finset.card_erase_add_one hi
      omega
    simp [createMode, creation, transition_apply, hi, hx _ hc]
  · simp [createMode, creation, transition_apply, hi]

theorem pairMode_sector {n N : ℕ} (a : PairIndex n) {x : Space n}
    (hx : InSector (N + 2) x) : InSector N (pairMode a x) :=
  annihilateMode_sector a.val.2 (annihilateMode_sector a.val.1 hx)

theorem pairKet_sector {n : ℕ} (a : PairIndex n) : InSector 2 (pairKet a) := by
  rw [pairKet, pairMode_adjoint]
  exact createMode_sector a.val.1 (createMode_sector a.val.2 (sector_ket ∅))

theorem pairEmbed_sector {n : ℕ} (p : PairSpace n) : InSector 2 (pairEmbed p) :=
  sector_sum _ _ fun a _ => sector_smul (p a) (pairKet_sector a)

theorem sector_orthogonal {n N K : ℕ} {x y : Space n} (hx : InSector N x)
    (hy : InSector K y) (hNK : N ≠ K) : inner ℂ x y = 0 := by
  rw [PiLp.inner_apply]
  apply Finset.sum_eq_zero
  intro A _
  by_cases hA : A.card = N
  · rw [hy A (by omega)]
    simp
  · rw [hx A hA]
    simp

theorem annihilateMode_sector_zero {n : ℕ} (i : Fin n) {x : Space n}
    (hx : InSector 0 x) : annihilateMode i x = 0 := by
  ext A
  by_cases hi : i ∈ A
  · simp [annihilateMode, annihilation, transition_apply, hi]
  · have hc : (insert i A).card ≠ 0 := by
      rw [Finset.card_insert_of_notMem hi]
      omega
    simp [annihilateMode, annihilation, transition_apply, hi, hx _ hc]

theorem pairMode_sector_zero {n : ℕ} (a : PairIndex n) {x : Space n}
    (hx : InSector 0 x) : pairMode a x = 0 := by
  simp [pairMode, Module.End.mul_apply, annihilateMode_sector_zero _ hx]

theorem pairMode_sector_one {n : ℕ} (a : PairIndex n) {x : Space n}
    (hx : InSector 1 x) : pairMode a x = 0 :=
  annihilateMode_sector_zero a.val.2 (annihilateMode_sector a.val.1 hx)

theorem pairCreate_sector {n N : ℕ} (p : PairSpace n) {x : Space n}
    (hx : InSector N x) : InSector (N + 2) (pairCreate p x) := by
  unfold pairCreate
  rw [LinearMap.sum_apply]
  apply sector_sum
  intro a _
  rw [LinearMap.smul_apply]
  apply sector_smul
  rw [pairMode_adjoint]
  exact createMode_sector a.val.1 (createMode_sector a.val.2 hx)

theorem pairLift_sector_zero {n : ℕ} (Q : Module.End ℂ (PairSpace n)) {x : Space n}
    (hx : InSector 0 x) : pairLift Q x = 0 := by
  simp [pairLift, LinearMap.sum_apply, Module.End.mul_apply, pairMode_sector_zero _ hx]

theorem pairLift_sector_one {n : ℕ} (Q : Module.End ℂ (PairSpace n)) {x : Space n}
    (hx : InSector 1 x) : pairLift Q x = 0 := by
  simp [pairLift, LinearMap.sum_apply, Module.End.mul_apply, pairMode_sector_one _ hx]

theorem pairLift_preserves_sector {n N : ℕ} (Q : Module.End ℂ (PairSpace n))
    {x : Space n} (hx : InSector N x) : InSector N (pairLift Q x) := by
  obtain _ | _ | N := N
  · rw [pairLift_sector_zero Q hx]; exact sector_zero
  · rw [pairLift_sector_one Q hx]; exact sector_zero
  · unfold pairLift
    rw [LinearMap.sum_apply]
    exact sector_sum _ _ fun a _ => pairCreate_sector _ (pairMode_sector a hx)

theorem createMode_ket {n : ℕ} (i : Fin n) (A : Finset (Fin n)) (hi : i ∉ A) :
    createMode i (ket A) = sign i A • ket (insert i A) := by
  ext B
  by_cases hB : i ∈ B
  · by_cases he : B.erase i = A
    · have hBA : B = insert i A := by rw [← he, Finset.insert_erase hB]
      subst B
      simp [createMode, creation, transition_apply, ket, hi]
    · have hBA : insert i A ≠ B := by
        intro h
        subst B
        simp [hi] at he
      simp [createMode, creation, transition_apply, ket, hB, he, hBA]
  · have hBA : insert i A ≠ B := by
      intro h
      rw [← h] at hB
      simp at hB
    simp [createMode, creation, transition_apply, ket, hB, hBA]

theorem pairKet_occupation {n : ℕ} (a : PairIndex n) :
    pairKet a = ket {a.val.1, a.val.2} := by
  rw [pairKet, pairMode_adjoint, Module.End.mul_apply,
    createMode_ket _ ∅ (by simp)]
  simp only [sign, Finset.filter_empty, Finset.card_empty, pow_zero, one_smul]
  rw [createMode_ket _ _ (by simpa using ne_of_lt a.property)]
  have hnot : ¬a.val.2 < a.val.1 := not_lt_of_ge (le_of_lt a.property)
  have hs : sign a.val.1 (insert a.val.2 ∅) = 1 := by
    unfold sign
    rw [Finset.filter_insert, ite_eq_right hnot]
    simp
  rw [hs, one_smul]
  rfl

def pairOccupation {n : ℕ} (a : PairIndex n) : Finset (Fin n) := {a.val.1, a.val.2}

theorem pairOccupation_card {n : ℕ} (a : PairIndex n) : (pairOccupation a).card = 2 := by
  simp [pairOccupation, ne_of_lt a.property]

theorem pairOccupation_injective {n : ℕ} : Function.Injective (pairOccupation (n := n)) := by
  intro a b hab
  have hket : pairKet a = pairKet b := by
    simpa only [pairKet_occupation, pairOccupation] using congrArg ket hab
  have hinner := pairKet_inner a b
  rw [hket, pairKet_inner] at hinner
  by_contra hne
  simp [hne] at hinner

theorem pairOccupation_surjective {n : ℕ} (A : Finset (Fin n)) (hA : A.card = 2) :
    ∃ a : PairIndex n, pairOccupation a = A := by
  obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp hA
  rcases lt_or_gt_of_ne hij with h | h
  · exact ⟨⟨(i, j), h⟩, rfl⟩
  · exact ⟨⟨(j, i), h⟩, Finset.pair_comm j i⟩

theorem pairEmbed_coefficient {n : ℕ} (p : PairSpace n) (a : PairIndex n) :
    pairEmbed p (pairOccupation a) = p a := by
  change (∑ b, p b • pairKet b) (pairOccupation a) = p a
  simp only [WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply,
    smul_eq_mul, pairKet_occupation]
  have heq (b : PairIndex n) :
      pairOccupation a = ({b.val.1, b.val.2} : Finset (Fin n)) ↔ a = b :=
    pairOccupation_injective.eq_iff
  simp [ket, heq]

theorem pairEmbed_range_iff {n : ℕ} (x : Space n) :
    (∃ p : PairSpace n, pairEmbed p = x) ↔ InSector 2 x := by
  constructor
  · rintro ⟨p, rfl⟩; exact pairEmbed_sector p
  · intro hx
    let p : PairSpace n := WithLp.toLp 2 (fun a => x (pairOccupation a))
    refine ⟨p, ?_⟩
    ext A
    by_cases hA : A.card = 2
    · obtain ⟨a, rfl⟩ := pairOccupation_surjective A hA
      exact pairEmbed_coefficient p a
    · rw [pairEmbed_sector p A hA, hx A hA]

theorem number_sector_iff {n N : ℕ} (x : Space n) :
    number n x = (N : ℂ) • x ↔ InSector N x := by
  constructor
  · intro h A hA
    have he := congrArg (fun y : Space n => y A) h
    change (A.card : ℂ) * x A = (N : ℂ) * x A at he
    have hne : (A.card : ℂ) ≠ (N : ℂ) := by exact_mod_cast hA
    exact (mul_eq_mul_right_iff.mp he).resolve_left hne
  · exact number_on_sector

theorem parity_norm {n : ℕ} (x : Space n) : ‖parity n x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp [EuclideanSpace.norm_sq_eq, parity_apply, norm_pow]

theorem parity_adjoint {n : ℕ} : (parity n).adjoint = parity n := by
  symm
  rw [LinearMap.eq_adjoint_iff]
  intro x y
  rw [PiLp.inner_apply, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro A _
  simp [parity_apply, RCLike.inner_apply]
  ring

end VortexGap.Fermion
