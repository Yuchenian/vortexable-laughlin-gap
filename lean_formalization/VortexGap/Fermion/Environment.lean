import VortexGap.Fermion.PairCovariance

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped BigOperators InnerProduct
open OAI.LaughlinGap.Occupation

/-- Environment modes precede system modes in the canonical order. -/
def occupationJoinEquiv (n m : ℕ) :
    (Finset (Fin n) × Finset (Fin m)) ≃ Finset (Fin (n+m)) :=
  Finset.sumEquiv.toEquiv.symm.trans (Equiv.finsetCongr finSumFinEquiv)

def joinOccupation {n m : ℕ} (A : Finset (Fin n)) (B : Finset (Fin m)) :
    Finset (Fin (n+m)) := occupationJoinEquiv n m (A,B)

theorem joinOccupation_map {n m : ℕ} (A : Finset (Fin n)) (B : Finset (Fin m)) :
    joinOccupation A B = (A.disjSum B).map finSumFinEquiv.toEmbedding := rfl

theorem joinOccupation_card {n m : ℕ} (A : Finset (Fin n)) (B : Finset (Fin m)) :
    (joinOccupation A B).card = A.card+B.card := by
  simp [joinOccupation_map]

theorem joinOccupation_mem_env {n m : ℕ} (A : Finset (Fin n)) (B : Finset (Fin m)) (i : Fin n) :
    Fin.castAdd m i ∈ joinOccupation A B ↔ i ∈ A := by
  change finSumFinEquiv (Sum.inl i) ∈ (A.disjSum B).map finSumFinEquiv.toEmbedding ↔ _
  simp

theorem joinOccupation_mem_sys {n m : ℕ} (A : Finset (Fin n)) (B : Finset (Fin m)) (i : Fin m) :
    Fin.natAdd n i ∈ joinOccupation A B ↔ i ∈ B := by
  change finSumFinEquiv (Sum.inr i) ∈ (A.disjSum B).map finSumFinEquiv.toEmbedding ↔ _
  simp

abbrev SplitSpace (n m : ℕ) := EuclideanSpace ℂ (Finset (Fin n) × Finset (Fin m))

/-- The Hilbert l2 factorization, represented by product occupation coordinates. -/
def fockSplit (n m : ℕ) : Space (n+m) ≃ₗᵢ[ℂ] SplitSpace n m :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (occupationJoinEquiv n m).symm

theorem fockSplit_apply {n m : ℕ} (x : Space (n+m)) (A : Finset (Fin n)) (B : Finset (Fin m)) :
    fockSplit n m x (A,B) = x (joinOccupation A B) := rfl

theorem fockSplit_ket {n m : ℕ} (A : Finset (Fin n)) (B : Finset (Fin m)) :
    fockSplit n m (ket (joinOccupation A B)) = PiLp.single 2 (A,B) 1 := by
  change fockSplit n m (PiLp.single 2 (occupationJoinEquiv n m (A,B)) 1) = _
  rw [fockSplit, LinearIsometryEquiv.piLpCongrLeft_single]
  simp

theorem joinOccupation_flip_env {n m : ℕ} (A : Finset (Fin n)) (B : Finset (Fin m)) (i : Fin n) :
    flip (Fin.castAdd m i) (joinOccupation A B) = joinOccupation (flip i A) B := by
  by_cases hi : i ∈ A
  · have he : (A.erase i).disjSum B = (A.disjSum B).erase (Sum.inl i) := by
      ext j
      cases j <;> simp
    rw [flip_of_mem ((joinOccupation_mem_env A B i).mpr hi), flip_of_mem hi]
    rw [joinOccupation_map, joinOccupation_map, he, Finset.map_erase]
    rfl
  · have he : (insert i A).disjSum B = insert (Sum.inl i) (A.disjSum B) := by
      ext j
      cases j <;> simp
    rw [flip_of_not_mem (fun h => hi ((joinOccupation_mem_env A B i).mp h)), flip_of_not_mem hi]
    rw [joinOccupation_map, joinOccupation_map, he, Finset.map_insert]
    rfl

theorem joinOccupation_flip_sys {n m : ℕ} (A : Finset (Fin n)) (B : Finset (Fin m)) (i : Fin m) :
    flip (Fin.natAdd n i) (joinOccupation A B) = joinOccupation A (flip i B) := by
  by_cases hi : i ∈ B
  · have he : A.disjSum (B.erase i) = (A.disjSum B).erase (Sum.inr i) := by
      ext j
      cases j <;> simp
    rw [flip_of_mem ((joinOccupation_mem_sys A B i).mpr hi), flip_of_mem hi]
    rw [joinOccupation_map, joinOccupation_map, he, Finset.map_erase]
    rfl
  · have he : A.disjSum (insert i B) = insert (Sum.inr i) (A.disjSum B) := by
      ext j
      cases j <;> simp
    rw [flip_of_not_mem (fun h => hi ((joinOccupation_mem_sys A B i).mp h)), flip_of_not_mem hi]
    rw [joinOccupation_map, joinOccupation_map, he, Finset.map_insert]
    rfl

theorem joinOccupation_sign_env {n m : ℕ} (A : Finset (Fin n)) (B : Finset (Fin m)) (i : Fin n) :
    sign (Fin.castAdd m i) (joinOccupation A B) = sign i A := by
  unfold sign
  rw [joinOccupation_map, Finset.filter_map, Finset.card_map]
  change (-1 : ℂ)^((A.disjSum B).filter (fun k => finSumFinEquiv k < Fin.castAdd m i)).card = _
  have he : (A.disjSum B).filter (fun k => finSumFinEquiv k < Fin.castAdd m i) =
      (A.filter (fun k => k < i)).disjSum (∅ : Finset (Fin m)) := by
    ext k
    cases k with
    | inl j => simp only [Finset.mem_filter, Finset.inl_mem_disjSum,
        finSumFinEquiv_apply_left, Fin.lt_def, Fin.val_castAdd]
    | inr j =>
      have hj : ¬ Fin.natAdd n j < Fin.castAdd m i := by
        simp only [Fin.lt_def, Fin.val_natAdd, Fin.val_castAdd]
        omega
      simp [hj]
  rw [he, Finset.card_disjSum, Finset.card_empty, Nat.add_zero]

theorem joinOccupation_sign_sys {n m : ℕ} (A : Finset (Fin n)) (B : Finset (Fin m)) (i : Fin m) :
    sign (Fin.natAdd n i) (joinOccupation A B) = (-1 : ℂ)^A.card * sign i B := by
  unfold sign
  rw [joinOccupation_map, Finset.filter_map, Finset.card_map]
  change (-1 : ℂ)^((A.disjSum B).filter (fun k => finSumFinEquiv k < Fin.natAdd n i)).card = _
  have he : (A.disjSum B).filter (fun k => finSumFinEquiv k < Fin.natAdd n i) =
      A.disjSum (B.filter (fun k => k < i)) := by
    ext k
    cases k with
    | inl j =>
      have hj : Fin.castAdd m j < Fin.natAdd n i := by
        simp only [Fin.lt_def, Fin.val_natAdd, Fin.val_castAdd]
        omega
      simp [hj]
    | inr j => simp only [Finset.mem_filter, Finset.inr_mem_disjSum,
        finSumFinEquiv_apply_right, Fin.lt_def, Fin.val_natAdd, Nat.add_lt_add_iff_left]
  rw [he, Finset.card_disjSum, pow_add]

theorem fockSplit_transition_env {n m : ℕ} (i : Fin n) (ε : Bool) (x : Space (n+m))
    (A : Finset (Fin n)) (B : Finset (Fin m)) :
    fockSplit n m (transition (Fin.castAdd m i) ε x) (A,B) =
      if decide (i ∈ A) = ε then sign i A * fockSplit n m x (flip i A,B) else 0 := by
  simp only [fockSplit_apply, transition_apply, joinOccupation_mem_env, joinOccupation_sign_env,
    joinOccupation_flip_env, fockSplit_apply]

theorem fockSplit_transition_sys {n m : ℕ} (i : Fin m) (ε : Bool) (x : Space (n+m))
    (A : Finset (Fin n)) (B : Finset (Fin m)) :
    fockSplit n m (transition (Fin.natAdd n i) ε x) (A,B) =
      (-1 : ℂ)^A.card *
        (if decide (i ∈ B) = ε then sign i B * fockSplit n m x (A,flip i B) else 0) := by
  simp only [fockSplit_apply, transition_apply, joinOccupation_mem_sys, joinOccupation_sign_sys,
    joinOccupation_flip_sys, fockSplit_apply]
  split_ifs <;> simp [mul_assoc]

/-- The actual environment vacuum inclusion in product occupation coordinates. -/
def environmentVacuum (n m : ℕ) : Space m →ₗ[ℂ] SplitSpace n m where
  toFun x := WithLp.toLp 2 (fun AB => if AB.1 = ∅ then x AB.2 else 0)
  map_add' x y := by
    ext AB
    change (if AB.1 = ∅ then (x+y) AB.2 else 0) = _
    split_ifs <;> simp_all
  map_smul' z x := by
    ext AB
    change (if AB.1 = ∅ then (z • x) AB.2 else 0) = _
    split_ifs <;> simp_all

theorem environmentVacuum_apply {n m : ℕ} (x : Space m)
    (A : Finset (Fin n)) (B : Finset (Fin m)) :
    environmentVacuum n m x (A,B) = if A = ∅ then x B else 0 := rfl

theorem environmentVacuum_inner {n m : ℕ} (x y : Space m) :
    inner ℂ (environmentVacuum n m x) (environmentVacuum n m y) = inner ℂ x y := by
  simp [PiLp.inner_apply, Fintype.sum_prod_type, environmentVacuum_apply]

def environmentVacuumIsometry (n m : ℕ) : Space m →ₗᵢ[ℂ] SplitSpace n m where
  toLinearMap := environmentVacuum n m
  norm_map' := (LinearMap.norm_map_iff_inner_map_map _).mpr environmentVacuum_inner

theorem environmentVacuum_sector {n m N : ℕ} {x : Space m} (hx : InSector N x) :
    InSector N ((fockSplit n m).symm (environmentVacuum n m x)) := by
  intro C hC
  obtain ⟨⟨A,B⟩, rfl⟩ := (occupationJoinEquiv n m).surjective C
  change ((fockSplit n m).symm (environmentVacuum n m x)) (joinOccupation A B) = 0
  rw [← fockSplit_apply, (fockSplit n m).apply_symm_apply, environmentVacuum_apply]
  by_cases hA : A = ∅
  · subst A
    change (joinOccupation (∅ : Finset (Fin n)) B).card ≠ N at hC
    have hB : B.card ≠ N := by
      simpa only [joinOccupation_card, Finset.card_empty, zero_add] using hC
    simp [hx B hB]
  · simp [hA]

end VortexGap.Fermion
