import VortexGap.Fermion.CountableEnvironmentProjection
import VortexGap.Examples.CountableFockExamples

noncomputable section
set_option autoImplicit false
namespace VortexGap.Examples
open Fermion
open scoped InnerProduct ComplexConjugate

theorem splitJoin_single_env (j : ℕ) :
    countableJoinImage ({j},∅) = countableKet {2*j} := by
  rw [countableJoinImage_product, countableOccupationOperator_singleton,
    countableOccupationImage_empty, countableEnvBasis, countableCreate_ket,
    countableCreateMode_ket _ ∅ (by simp)]
  simp [countableSign, Equiv.natSumNatEquivNat_apply]

theorem splitJoin_single_sys (j : ℕ) :
    countableJoinImage (∅,{j}) = countableKet {2*j+1} := by
  rw [countableJoinImage_product, countableOccupationOperator_empty,
    countableOccupationImage_singleton, countableSysBasis, countableCreate_ket,
    countableCreateMode_ket _ ∅ (by simp)]
  simp [countableSign, Equiv.natSumNatEquivNat_apply]

theorem splitJoin_inverted_pair :
    countableFockJoin (countableSplitKet ({1},{0})) = -countableKet {1,2} := by
  rw [countableFockJoin_ket, countableJoinImage_product, countableOccupationOperator_singleton,
    countableOccupationImage_singleton]
  change countableCreate (orbitalKet 2) (countableCreate (orbitalKet 1) (countableKet ∅)) = _
  rw [countableCreate_ket, countableCreate_ket,
    countableCreateMode_ket 1 ∅ (by simp), Finset.insert_empty, map_smul,
    countableCreateMode_ket 2 {1} (by simp)]
  norm_num [countableSign, Finset.filter_singleton, Finset.pair_comm]

theorem splitPair_annihilate_sys :
    countableSplitConjugate (countableAnnihilate (countableSysBasis 0))
      (countableSplitKet ({0},{0})) = -countableSplitKet ({0},∅) := by
  rw [countableSplitConjugate_apply, countableFockJoin_ket,
    countableJoinImage_annihilate_sys_of_mem 0 {0} {0} (by simp),
    map_smul, countableFockSplit_image]
  norm_num [countableSign]

theorem splitPair_annihilate_env :
    countableSplitConjugate (countableAnnihilate (countableEnvBasis 0))
      (countableSplitKet ({0},{0})) = countableSplitKet (∅,{0}) := by
  rw [countableSplitConjugate_apply, countableFockJoin_ket,
    countableJoinImage_annihilate_env_of_mem 0 {0} {0} (by simp),
    map_smul, countableFockSplit_image]
  norm_num [countableSign]

theorem splitPair_create_sys :
    countableSplitConjugate (countableCreate (countableSysBasis 0))
      (countableSplitKet ({0},∅)) = -countableSplitKet ({0},{0}) := by
  rw [countableSplitConjugate_apply, countableFockJoin_ket,
    countableJoinImage_create_sys_of_not_mem 0 {0} ∅ (by simp),
    map_smul, countableFockSplit_image]
  norm_num [countableSign]

theorem splitPair_imaginary_annihilation :
    countableSplitConjugate (countableAnnihilate (Complex.I • countableSysBasis 0))
      (countableSplitKet ({0},{0})) = Complex.I • countableSplitKet ({0},∅) := by
  rw [countableSplitConjugate_apply, countableAnnihilate_smul,
    ContinuousLinearMap.smul_apply, map_smul]
  change conj Complex.I •
    countableSplitConjugate (countableAnnihilate (countableSysBasis 0))
      (countableSplitKet ({0},{0})) = _
  rw [splitPair_annihilate_sys]
  simp

theorem splitThree_annihilate_sys :
    countableSplitConjugate (countableAnnihilate (countableSysBasis 0))
      (countableSplitKet ({0,1},{0})) = countableSplitKet ({0,1},∅) := by
  rw [countableSplitConjugate_apply, countableFockJoin_ket,
    countableJoinImage_annihilate_sys_of_mem 0 {0,1} {0} (by simp),
    map_smul, countableFockSplit_image]
  norm_num [countableSign]

def splitGeometricState : CountableSplitSpace := countableFockSplit geometricOneParticle

theorem splitGeometricState_norm_sq : ‖splitGeometricState‖ ^ 2 = (4/3 : ℝ) := by
  rw [splitGeometricState, countableFockSplit_norm, geometricOneParticle_norm_sq]

theorem splitGeometricState_sector : splitGeometricState ∈ countableSplitSector 1 :=
  countableFockSplit_sector geometricOneParticle_sector

theorem splitGeometricState_env_coefficient (j : ℕ) :
    splitGeometricState ({j},∅) = (Complex.I / 2 : ℂ)^(2*j) := by
  rw [splitGeometricState, countableFockSplit_coefficient, splitJoin_single_env,
    countableKet_inner_left, geometricOneParticle, createVacuum_singleton_coefficient,
    geometricOrbital_coefficient]

theorem splitGeometricState_sys_coefficient (j : ℕ) :
    splitGeometricState (∅,{j}) = (Complex.I / 2 : ℂ)^(2*j+1) := by
  rw [splitGeometricState, countableFockSplit_coefficient, splitJoin_single_sys,
    countableKet_inner_left, geometricOneParticle, createVacuum_singleton_coefficient,
    geometricOrbital_coefficient]

theorem splitGeometricState_env_coefficient_ne_zero (j : ℕ) :
    splitGeometricState ({j},∅) ≠ 0 := by
  rw [splitGeometricState_env_coefficient]
  exact pow_ne_zero _ (by norm_num)

theorem splitGeometricState_sys_coefficient_ne_zero (j : ℕ) :
    splitGeometricState (∅,{j}) ≠ 0 := by
  rw [splitGeometricState_sys_coefficient]
  exact pow_ne_zero _ (by norm_num)

theorem splitGeometricState_decomposition :
    countableEnvironmentProjection 0 splitGeometricState +
      countableEnvironmentProjection 1 splitGeometricState = splitGeometricState := by
  simpa [Finset.sum_range_succ] using countableEnvironmentProjection_sum splitGeometricState_sector

theorem splitGeometricState_no_two_environment :
    countableEnvironmentProjection 2 splitGeometricState = 0 :=
  countableEnvironmentProjection_above_total splitGeometricState_sector (by norm_num)

theorem splitGeometricState_orthogonal_components :
    inner ℂ (countableEnvironmentProjection 0 splitGeometricState)
      (countableEnvironmentProjection 1 splitGeometricState) = 0 :=
  countableEnvironmentProjection_orthogonal 0 1 _ _ (by norm_num)


theorem splitGeometricState_environment_component_ne_zero :
    countableEnvironmentProjection 1 splitGeometricState ≠ 0 := by
  intro h
  apply splitGeometricState_env_coefficient_ne_zero 0
  have hz := congrArg (fun x : CountableSplitSpace => x ({0},∅)) h
  simpa only [countableEnvironmentProjection_apply, Finset.card_singleton, ite_true,
    lp.coeFn_zero, Pi.zero_apply] using hz

theorem splitGeometricState_system_component_ne_zero :
    countableEnvironmentProjection 0 splitGeometricState ≠ 0 := by
  intro h
  apply splitGeometricState_sys_coefficient_ne_zero 0
  have hz := congrArg (fun x : CountableSplitSpace => x (∅,{0})) h
  simpa only [countableEnvironmentProjection_apply, Finset.card_empty, ite_true,
    lp.coeFn_zero, Pi.zero_apply] using hz

end VortexGap.Examples
