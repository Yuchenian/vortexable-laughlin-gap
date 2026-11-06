import VortexGap.Fermion.CountableSplitActions

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped InnerProduct ComplexConjugate

def countableSplitConjugate (T : CountableSpace →L[ℂ] CountableSpace) :
    CountableSplitSpace →L[ℂ] CountableSplitSpace :=
  countableFockSplit.toLinearIsometry.toContinuousLinearMap.comp (T.comp countableFockJoin.toLinearIsometry.toContinuousLinearMap)

theorem countableSplitConjugate_apply (T : CountableSpace →L[ℂ] CountableSpace)
    (x : CountableSplitSpace) :
    countableSplitConjugate T x = countableFockSplit (T (countableFockJoin x)) := rfl

theorem countableJoinImage_inner_join (AB : Finset ℕ × Finset ℕ) (x : CountableSplitSpace) :
    inner ℂ (countableJoinImage AB) (countableFockJoin x) = x AB := by
  rw [← countableFockJoin_ket, countableFockJoin.inner_map_map, countableSplitKet_inner_left]

theorem countableAnnihilate_inner (v : CountableOrbital) (x y : CountableSpace) :
    inner ℂ (countableAnnihilate v x) y = inner ℂ x (countableCreate v y) :=
  ContinuousLinearMap.adjoint_inner_left (countableCreate v) y x

/-- Full completed-space coordinate identity for c_env^dagger = c^dagger tensor I. -/
theorem countableSplit_create_env_coordinate (j : ℕ) (x : CountableSplitSpace)
    (A B : Finset ℕ) :
    countableSplitConjugate (countableCreate (countableEnvBasis j)) x (A,B) =
      if j ∈ A then countableSign j A * x (A.erase j,B) else 0 := by
  rw [countableSplitConjugate_apply, countableFockSplit_coefficient, ← countableAnnihilate_inner]
  by_cases hj : j ∈ A
  · rw [countableJoinImage_annihilate_env_of_mem j A B hj, inner_smul_left,
      countableJoinImage_inner_join, countableSign_conj, ite_eq_left hj]
  · rw [countableJoinImage_annihilate_env_of_not_mem j A B hj, inner_zero_left, ite_eq_right hj]

theorem countableSplit_annihilate_env_coordinate (j : ℕ) (x : CountableSplitSpace)
    (A B : Finset ℕ) :
    countableSplitConjugate (countableAnnihilate (countableEnvBasis j)) x (A,B) =
      if j ∈ A then 0 else countableSign j A * x (insert j A,B) := by
  rw [countableSplitConjugate_apply, countableFockSplit_coefficient, ← countableCreate_inner]
  by_cases hj : j ∈ A
  · rw [countableJoinImage_create_env_of_mem j A B hj, inner_zero_left, ite_eq_left hj]
  · rw [countableJoinImage_create_env_of_not_mem j A B hj, inner_smul_left,
      countableJoinImage_inner_join, countableSign_conj, ite_eq_right hj]

/-- Full completed-space coordinate identity for c_sys^dagger = parity_env tensor c^dagger. -/
theorem countableSplit_create_sys_coordinate (j : ℕ) (x : CountableSplitSpace)
    (A B : Finset ℕ) :
    countableSplitConjugate (countableCreate (countableSysBasis j)) x (A,B) =
      if j ∈ B then ((-1 : ℂ)^A.card * countableSign j B) * x (A,B.erase j) else 0 := by
  rw [countableSplitConjugate_apply, countableFockSplit_coefficient, ← countableAnnihilate_inner]
  by_cases hj : j ∈ B
  · rw [countableJoinImage_annihilate_sys_of_mem j A B hj, inner_smul_left,
      countableJoinImage_inner_join, ite_eq_left hj]
    simp only [map_mul, map_pow, map_neg, map_one, countableSign_conj]
  · rw [countableJoinImage_annihilate_sys_of_not_mem j A B hj, inner_zero_left, ite_eq_right hj]

theorem countableSplit_annihilate_sys_coordinate (j : ℕ) (x : CountableSplitSpace)
    (A B : Finset ℕ) :
    countableSplitConjugate (countableAnnihilate (countableSysBasis j)) x (A,B) =
      if j ∈ B then 0 else ((-1 : ℂ)^A.card * countableSign j B) * x (A,insert j B) := by
  rw [countableSplitConjugate_apply, countableFockSplit_coefficient, ← countableCreate_inner]
  by_cases hj : j ∈ B
  · rw [countableJoinImage_create_sys_of_mem j A B hj, inner_zero_left, ite_eq_left hj]
  · rw [countableJoinImage_create_sys_of_not_mem j A B hj, inner_smul_left,
      countableJoinImage_inner_join, ite_eq_right hj]
    simp only [map_mul, map_pow, map_neg, map_one, countableSign_conj]

theorem countableSplitConjugate_comp (S T : CountableSpace →L[ℂ] CountableSpace) :
    countableSplitConjugate (S.comp T) =
      (countableSplitConjugate S).comp (countableSplitConjugate T) := by
  apply ContinuousLinearMap.ext
  intro x
  change countableFockSplit (S (T (countableFockJoin x))) =
    countableFockSplit (S (countableFockJoin (countableFockSplit (T (countableFockJoin x)))))
  rw [show countableFockJoin (countableFockSplit _) = _ from countableFockJoin.apply_symm_apply _]

theorem countableSplitConjugate_id :
    countableSplitConjugate (1 : CountableSpace →L[ℂ] CountableSpace) = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  exact countableFockJoin.symm_apply_apply x

end VortexGap.Fermion
