import VortexGap.Fermion.FiniteLoss

/-! Actual reference pair interactions on every spectator occupation. -/
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped BigOperators InnerProduct ComplexConjugate
open OAI.LaughlinGap.Occupation

def referenceAmplification (n m : ℕ) : Module.End ℂ (Space n) →ₗ[ℂ] Module.End ℂ (SplitSpace n m) where
  toFun H := referenceAmplify H
  map_add' H K := by ext x AB; rfl
  map_smul' z H := by ext x AB; rfl

theorem referenceAmplify_adjoint {n m : ℕ} (H : Module.End ℂ (Space n)) :
    referenceAmplify (m := m) H.adjoint = (referenceAmplify (m := m) H).adjoint := by
  rw [LinearMap.eq_adjoint_iff]
  intro x y
  have he : inner ℂ (referenceAmplify H.adjoint x) y =
      ∑ B, inner ℂ (H.adjoint (referenceSlice B x)) (referenceSlice B y) := by
    simp only [PiLp.inner_apply, Fintype.sum_prod_type, referenceAmplify_apply, referenceSlice_apply]
    rw [Finset.sum_comm]
  rw [he, referenceAmplify_inner]
  exact Finset.sum_congr rfl fun _ _ => LinearMap.adjoint_inner_left _ _ _

theorem create_orbitalEnv {n m : ℕ} (v : EuclideanSpace ℂ (Fin n)) :
    create (orbitalEnv n m v) = ∑ i, v i • createMode (Fin.castAdd m i) := by
  unfold create
  rw [Fin.sum_univ_add]
  simp only [orbitalEnv_left, orbitalEnv_right, zero_smul, Finset.sum_const_zero, add_zero]

theorem annihilate_orbitalEnv {n m : ℕ} (v : EuclideanSpace ℂ (Fin n)) :
    annihilate (orbitalEnv n m v) = ∑ i, conj (v i) • annihilateMode (Fin.castAdd m i) := by
  unfold annihilate
  rw [Fin.sum_univ_add]
  simp only [orbitalEnv_left, orbitalEnv_right, map_zero, zero_smul, Finset.sum_const_zero, add_zero]

theorem create_orbitalSys {n m : ℕ} (v : EuclideanSpace ℂ (Fin m)) :
    create (orbitalSys n m v) = ∑ i, v i • createMode (Fin.natAdd n i) := by
  unfold create
  rw [Fin.sum_univ_add]
  simp only [orbitalSys_left, orbitalSys_right, zero_smul, Finset.sum_const_zero, zero_add]

theorem annihilate_orbitalSys {n m : ℕ} (v : EuclideanSpace ℂ (Fin m)) :
    annihilate (orbitalSys n m v) = ∑ i, conj (v i) • annihilateMode (Fin.natAdd n i) := by
  unfold annihilate
  rw [Fin.sum_univ_add]
  simp only [orbitalSys_left, orbitalSys_right, map_zero, zero_smul, Finset.sum_const_zero, zero_add]

theorem fockSplit_create_env {n m : ℕ} (v : EuclideanSpace ℂ (Fin n)) (x : Space (n+m)) :
    fockSplit n m (create (orbitalEnv n m v) x) = referenceAmplify (create v) (fockSplit n m x) := by
  ext ⟨A,B⟩
  rw [create_orbitalEnv, referenceAmplify_apply]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
    WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, createMode, creation,
    create, transition_apply, referenceSlice_apply, fockSplit_apply,
    joinOccupation_mem_env, joinOccupation_sign_env, joinOccupation_flip_env]

theorem fockSplit_annihilate_env {n m : ℕ} (v : EuclideanSpace ℂ (Fin n)) (x : Space (n+m)) :
    fockSplit n m (annihilate (orbitalEnv n m v) x) =
      referenceAmplify (annihilate v) (fockSplit n m x) := by
  ext ⟨A,B⟩
  rw [annihilate_orbitalEnv, referenceAmplify_apply]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
    WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, annihilateMode, annihilation,
    annihilate, transition_apply, referenceSlice_apply, fockSplit_apply,
    joinOccupation_mem_env, joinOccupation_sign_env, joinOccupation_flip_env]

theorem fockSplit_pairCreate_env {n m : ℕ} (p : PairSpace n) (x : Space (n+m)) :
    fockSplit n m (pairCreate (exteriorSquare (orbitalEnv n m).toLinearMap p) x) =
      referenceAmplify (pairCreate p) (fockSplit n m x) := by
  have hb (b : PairIndex n) :
      fockSplit n m (pairCreate (exteriorSquare (orbitalEnv n m).toLinearMap (pairBasis b)) x) =
        referenceAmplify (pairCreate (pairBasis b)) (fockSplit n m x) := by
    rw [← wedgePair_basis b, exteriorSquare_wedge, pairCreate_wedge, pairCreate_wedge,
      referenceAmplify_mul]
    change fockSplit n m
        (create (orbitalEnv n m (PiLp.single 2 b.val.1 1))
          (create (orbitalEnv n m (PiLp.single 2 b.val.2 1)) x)) = _
    simp only [fockSplit_create_env, Module.End.mul_apply]
  change fockSplit n m (pairCreation (n+m) (exteriorSquare (orbitalEnv n m).toLinearMap p) x) =
    referenceAmplification n m (pairCreation n p) (fockSplit n m x)
  conv_lhs => rw [← pairBasis_expansion p]
  conv_rhs => rw [← pairBasis_expansion p]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  exact Finset.sum_congr rfl fun b _ => congrArg (fun y : SplitSpace n m => p b • y) (hb b)

theorem fockSplit_pairAnnihilate_env {n m : ℕ} (p : PairSpace n) (x : Space (n+m)) :
    fockSplit n m (pairAnnihilate (exteriorSquare (orbitalEnv n m).toLinearMap p) x) =
      referenceAmplify (pairAnnihilate p) (fockSplit n m x) := by
  apply ext_inner_left ℂ
  intro y
  obtain ⟨z,rfl⟩ := (fockSplit n m).surjective y
  rw [(fockSplit n m).inner_map_map]
  rw [← LinearMap.adjoint_inner_left (pairAnnihilate (exteriorSquare (orbitalEnv n m).toLinearMap p)) x z,
    pairAnnihilate_adjoint]
  rw [← LinearMap.adjoint_inner_left (referenceAmplify (m := m) (pairAnnihilate p)),
    ← referenceAmplify_adjoint, pairAnnihilate_adjoint]
  rw [← fockSplit_pairCreate_env, (fockSplit n m).inner_map_map]

theorem fockSplit_pairInteraction_env {n m : ℕ} (p : PairSpace n) (x : Space (n+m)) :
    fockSplit n m (pairLift (pairRankOne (exteriorSquare (orbitalEnv n m).toLinearMap p)) x) =
      referenceAmplify (pairLift (pairRankOne p)) (fockSplit n m x) := by
  rw [pairLift_rankOne, pairLift_rankOne, pairAnnihilate_adjoint, pairAnnihilate_adjoint,
    referenceAmplify_mul]
  simp only [Module.End.mul_apply, fockSplit_pairCreate_env, fockSplit_pairAnnihilate_env]

/-- The reference pair interaction acts on every spectator occupation, not just spectator vacuum. -/
theorem fockSplit_frameInteraction_env {n m : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (p : ι → PairSpace n) (x : Space (n+m)) :
    fockSplit n m (pairLift (∑ i, (w i : ℂ) • pairRankOne (exteriorSquare (orbitalEnv n m).toLinearMap (p i))) x) =
      referenceAmplify (pairLift (∑ i, (w i : ℂ) • pairRankOne (p i))) (fockSplit n m x) := by
  change fockSplit n m
    (pairLiftLinear (n+m) (∑ i, (w i : ℂ) • pairRankOne (exteriorSquare (orbitalEnv n m).toLinearMap (p i))) x) =
    referenceAmplification n m (pairLiftLinear n (∑ i, (w i : ℂ) • pairRankOne (p i))) (fockSplit n m x)
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  exact Finset.sum_congr rfl fun i _ => congrArg (fun y : SplitSpace n m => (w i : ℂ) • y)
    (fockSplit_pairInteraction_env (p i) x)

end VortexGap.Fermion
