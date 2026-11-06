import VortexGap.Fermion.PairBounds

/-! Five-mode, three-particle checks, including a non-self-adjoint pair operator.
These are normalization and operator-interface regressions, not gap-transfer examples. -/
noncomputable section
set_option autoImplicit false
namespace VortexGap.Examples
open VortexGap.Fermion OAI.LaughlinGap.Occupation
open scoped InnerProduct ComplexConjugate

def threeParticleState : Space 5 :=
  (3 / 5 : ℂ) • ket {0, 1, 2} + (4 / 5 * Complex.I : ℂ) • ket {0, 3, 4}

theorem threeParticleState_inner : inner ℂ threeParticleState threeParticleState = 1 := by
  have hne : ({0, 1, 2} : Finset (Fin 5)) ≠ {0, 3, 4} := by decide
  simp only [threeParticleState, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right]
  norm_num [ket, EuclideanSpace.inner_single_left, PiLp.single_apply, map_ofNat, hne, Ne.symm hne]
  ring_nf
  norm_num

theorem threeParticleState_sector : InSector 3 threeParticleState := by
  apply sector_add
  · apply sector_smul
    convert sector_ket ({0, 1, 2} : Finset (Fin 5)) using 1; norm_num
  · apply sector_smul
    convert sector_ket ({0, 3, 4} : Finset (Fin 5)) using 1; norm_num

theorem threeParticleState_pair_count : ‖pairStack threeParticleState‖ ^ 2 = 3 := by
  rw [pairStack_norm_sq, sum_pairMode_norm_sq threeParticleState_sector]
  have h : ‖threeParticleState‖ ^ 2 = (1 : ℝ) := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), threeParticleState_inner]
    simp
  norm_num [h]

def pairTarget5 : PairIndex 5 := ⟨(1, 2), by decide⟩
def pairSource5 : PairIndex 5 := ⟨(3, 4), by decide⟩

def pairTransfer5 : Module.End ℂ (PairSpace 5) :=
  (InnerProductSpace.rankOne ℂ (pairBasis pairTarget5) (pairBasis pairSource5)).toLinearMap

theorem pairTransfer5_norm : ‖LinearMap.toContinuousLinearMap pairTransfer5‖ = 1 := by
  change ‖InnerProductSpace.rankOne ℂ (pairBasis pairTarget5) (pairBasis pairSource5)‖ = 1
  simp [pairBasis]

theorem pairTransfer5_not_selfadjoint : pairTransfer5.adjoint ≠ pairTransfer5 := by
  intro he
  have h := congrArg (fun A : Module.End ℂ (PairSpace 5) =>
    inner ℂ (pairBasis pairTarget5) (A (pairBasis pairSource5))) he
  rw [LinearMap.adjoint_inner_right] at h
  norm_num [pairTransfer5, pairBasis, InnerProductSpace.rankOne_apply,
    EuclideanSpace.inner_single_left, PiLp.single_apply, pairTarget5, pairSource5] at h

theorem pairTransfer5_state_action :
    pairLift pairTransfer5 threeParticleState =
      (4 / 5 * Complex.I : ℂ) • (ket {0, 1, 2} : Space 5) := by
  rw [pairTransfer5, pairLift_outer, pairCreate_basis, pairAnnihilate_basis, pairMode_adjoint]
  ext A
  fin_cases A <;>
    norm_num [pairMode, pairTarget5, pairSource5, threeParticleState,
      annihilateMode, createMode, annihilation, creation, Module.End.mul_apply,
      transition_apply, ket, OAI.LaughlinGap.Occupation.flip, sign,
      Finset.filter_insert, Finset.filter_singleton, Finset.ext_iff,
      Fin.forall_fin_succ, Finset.filter, Finset.card, Multiset.filter_singleton]

theorem pairTransfer5_sector_bound : ‖pairLiftSector 3 pairTransfer5‖ ≤ 3 := by
  have h := pairLiftSector_opNorm_le (N := 3) pairTransfer5
  norm_num [pairTransfer5_norm] at h ⊢
  exact h

end VortexGap.Examples
