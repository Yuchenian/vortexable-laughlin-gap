import VortexGap.Fermion.ReferencePair

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped BigOperators InnerProduct ComplexConjugate
open OAI.LaughlinGap.Occupation

/-- The actual product of environment and system occupation amplitudes. -/
def fockProduct {n m : ℕ} : Space n →ₗ[ℂ] Space m →ₗ[ℂ] SplitSpace n m where
  toFun u := {
    toFun := fun x => WithLp.toLp 2 (fun AB => u AB.1 * x AB.2)
    map_add' := by intro x y; ext AB; simp [mul_add]
    map_smul' := by intro z x; ext AB; simp [mul_left_comm] }
  map_add' := by intro u v; ext x AB; simp [add_mul]
  map_smul' := by intro z u; ext x AB; simp [mul_assoc]

theorem fockProduct_apply {n m : ℕ} (u : Space n) (x : Space m)
    (A : Finset (Fin n)) (B : Finset (Fin m)) :
    fockProduct u x (A,B) = u A * x B := rfl

theorem fockProduct_inner {n m : ℕ} (u v : Space n) (x y : Space m) :
    inner ℂ (fockProduct u x) (fockProduct v y) = inner ℂ u v * inner ℂ x y := by
  simp only [PiLp.inner_apply, Fintype.sum_prod_type, fockProduct_apply,
    RCLike.inner_apply, map_mul, Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro A _
  apply Finset.sum_congr rfl
  intro B _
  ring

theorem fockProduct_vacuum {n m : ℕ} (x : Space m) :
    fockProduct (ket (∅ : Finset (Fin n))) x = environmentVacuum n m x := by
  ext ⟨A,B⟩
  simp only [fockProduct_apply, environmentVacuum_apply, ket, PiLp.single_apply]
  split_ifs <;> simp_all

theorem referenceSlice_product {n m : ℕ} (u : Space n) (x : Space m) (B : Finset (Fin m)) :
    referenceSlice B (fockProduct u x) = x B • u := by
  ext A
  simp only [referenceSlice_apply, fockProduct_apply, PiLp.smul_apply, smul_eq_mul, mul_comm]

theorem referenceAmplify_product {n m : ℕ} (H : Module.End ℂ (Space n)) (u : Space n) (x : Space m) :
    referenceAmplify H (fockProduct u x) = fockProduct (H u) x := by
  ext ⟨A,B⟩
  rw [referenceAmplify_apply, referenceSlice_product, map_smul]
  simp only [fockProduct_apply, PiLp.smul_apply, smul_eq_mul, mul_comm]

theorem fockSplit_create_env_product {n m : ℕ}
    (v : EuclideanSpace ℂ (Fin n)) (u : Space n) (x : Space m) :
    fockSplit n m (create (orbitalEnv n m v) ((fockSplit n m).symm (fockProduct u x))) =
      fockProduct (create v u) x := by
  rw [fockSplit_create_env, (fockSplit n m).apply_symm_apply, referenceAmplify_product]

theorem fockSplit_annihilate_env_product {n m : ℕ}
    (v : EuclideanSpace ℂ (Fin n)) (u : Space n) (x : Space m) :
    fockSplit n m (annihilate (orbitalEnv n m v) ((fockSplit n m).symm (fockProduct u x))) =
      fockProduct (annihilate v u) x := by
  rw [fockSplit_annihilate_env, (fockSplit n m).apply_symm_apply, referenceAmplify_product]

theorem fockSplit_transition_sys_product {n m : ℕ}
    (i : Fin m) (ε : Bool) (u : Space n) (x : Space m) :
    fockSplit n m (transition (Fin.natAdd n i) ε ((fockSplit n m).symm (fockProduct u x))) =
      fockProduct (parity n u) (transition i ε x) := by
  ext ⟨A,B⟩
  rw [fockSplit_transition_sys]
  simp only [(fockSplit n m).apply_symm_apply, fockProduct_apply, parity_apply, transition_apply]
  split_ifs <;> ring

theorem fockSplit_create_sys_product {n m : ℕ}
    (v : EuclideanSpace ℂ (Fin m)) (u : Space n) (x : Space m) :
    fockSplit n m (create (orbitalSys n m v) ((fockSplit n m).symm (fockProduct u x))) =
      fockProduct (parity n u) (create v x) := by
  rw [create_orbitalSys]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
    createMode, creation, fockSplit_transition_sys_product, create]

theorem fockSplit_annihilate_sys_product {n m : ℕ}
    (v : EuclideanSpace ℂ (Fin m)) (u : Space n) (x : Space m) :
    fockSplit n m (annihilate (orbitalSys n m v) ((fockSplit n m).symm (fockProduct u x))) =
      fockProduct (parity n u) (annihilate v x) := by
  rw [annihilate_orbitalSys]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
    annihilateMode, annihilation, fockSplit_transition_sys_product, annihilate]

/-- Support in an actual environment-number sector, with unrestricted system state. -/
def environmentSector (n m K : ℕ) : Submodule ℂ (SplitSpace n m) where
  carrier := {x | ∀ A B, A.card ≠ K → x (A,B) = 0}
  zero_mem' := by intro A B _; rfl
  add_mem' := by intro x y hx hy A B hA; change x (A,B) + y (A,B) = 0; rw [hx A B hA, hy A B hA, add_zero]
  smul_mem' := by intro z x hx A B hA; change z * x (A,B) = 0; rw [hx A B hA, mul_zero]

theorem fockProduct_environmentSector {n m K : ℕ} {u : Space n} (hu : InSector K u) (x : Space m) :
    fockProduct u x ∈ environmentSector n m K := by
  intro A B hA
  rw [fockProduct_apply, hu A hA, zero_mul]

theorem environmentSector_orthogonal {n m K L : ℕ} {x y : SplitSpace n m}
    (hx : x ∈ environmentSector n m K) (hy : y ∈ environmentSector n m L) (hKL : K ≠ L) :
    inner ℂ x y = 0 := by
  simp only [PiLp.inner_apply, Fintype.sum_prod_type]
  apply Finset.sum_eq_zero
  intro A _
  apply Finset.sum_eq_zero
  intro B _
  by_cases hA : A.card = K
  · rw [hy A B (by omega), inner_zero_right]
  · rw [hx A B hA, inner_zero_left]

end VortexGap.Fermion
