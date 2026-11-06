import VortexGap.Fermion.CountablePairLimits
import VortexGap.Examples.CountablePairs

noncomputable section
set_option autoImplicit false
namespace VortexGap.Examples
open Fermion
open scoped InnerProduct

def geometricPairSector : countableSector 2 := ⟨geometricPairState, geometricPairState_sector⟩

def geometricPairHamiltonian : countableSector 2 →L[ℂ] countableSector 2 :=
  countablePairLift 2 (InnerProductSpace.rankOne ℂ geometricPair geometricPair)

theorem geometricPairSector_norm_sq : ‖geometricPairSector‖ ^ 2 = (1 / 3 : ℝ) :=
  geometricPairState_norm_sq

theorem geometricPairHamiltonian_positive : geometricPairHamiltonian.IsPositive :=
  countablePairLift_positive 2 _ (InnerProductSpace.isPositive_rankOne_self _)

theorem geometricPairHamiltonian_action :
    geometricPairHamiltonian geometricPairSector = (1 / 3 : ℂ) • geometricPairSector := by
  have hx : geometricPairSector =
      (⟨countablePairEmbedding geometricPair, countablePairEmbedding_sector geometricPair⟩ : countableSector 2) :=
    Subtype.ext geometricPair_embedding.symm
  rw [geometricPairHamiltonian, hx, countablePairLift_pairEmbedding]
  apply Subtype.ext
  change countablePairEmbedding ((inner ℂ geometricPair geometricPair) • geometricPair) = _
  rw [map_smul, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, geometricPair_norm_sq]
  norm_num

theorem geometricPairHamiltonian_energy :
    (inner ℂ geometricPairSector (geometricPairHamiltonian geometricPairSector)).re = (1 / 9 : ℝ) := by
  rw [geometricPairHamiltonian_action]
  change (inner ℂ geometricPairState ((1 / 3 : ℂ) • geometricPairState)).re = _
  rw [inner_smul_right, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, geometricPairState_norm_sq]
  norm_num

theorem geometricPairHamiltonian_nonzero : geometricPairHamiltonian ≠ 0 := by
  intro h
  have he := geometricPairHamiltonian_energy
  rw [h] at he
  norm_num at he

theorem geometricPairLift_complex_action :
    countablePairLift 2 (Complex.I • InnerProductSpace.rankOne ℂ geometricPair geometricPair)
      geometricPairSector = (Complex.I / 3) • geometricPairSector := by
  rw [countablePairLift_smul]
  change Complex.I • (geometricPairHamiltonian geometricPairSector) = _
  rw [geometricPairHamiltonian_action, smul_smul]
  congr 1
  ring

def lowPairVector : CountablePairSpace := lp.single 2 ⟨(0, 1), by omega⟩ 1

def threeParticlePairState (j : ℕ) : countableSector 3 :=
  ⟨countableKet {0, 1, j + 2}, by
    have hc : ({0, 1, j + 2} : Finset ℕ).card = 3 := by
      simp
    simpa only [hc] using countableKet_sector {0, 1, j + 2}⟩

theorem threeParticlePairState_norm (j : ℕ) : ‖threeParticlePairState j‖ = 1 :=
  countableKet_norm _

theorem lowPairVector_annihilate_three (j : ℕ) :
    countablePairAnnihilate 3 lowPairVector (threeParticlePairState j) = countableKet {j + 2} := by
  rw [lowPairVector, countablePairAnnihilate_single]
  simp only [map_one, one_smul]
  have h0 : countableAnnihilateMode 0 (countableKet {0, 1, j + 2}) = countableKet {1, j + 2} := by
    rw [countableAnnihilateMode_ket 0 _ (by simp)]
    simp [countableSign]
  change countableAnnihilateMode 1
    (countableAnnihilateMode 0 (countableKet {0, 1, j + 2})) = _
  rw [h0, countableAnnihilateMode_ket 1 _ (by simp)]
  simp [countableSign, Finset.filter_insert, Finset.filter_singleton]

theorem threeParticlePairLift_energy (j : ℕ) :
    (inner ℂ (threeParticlePairState j)
      (countablePairLift 3 (InnerProductSpace.rankOne ℂ lowPairVector lowPairVector)
        (threeParticlePairState j))).re = 1 := by
  rw [countablePairLift_rankOne]
  change (inner ℂ (threeParticlePairState j) ((countablePairAnnihilate 3 lowPairVector).adjoint
    (countablePairAnnihilate 3 lowPairVector (threeParticlePairState j)))).re = _
  rw [ContinuousLinearMap.adjoint_inner_right, lowPairVector_annihilate_three,
    inner_self_eq_norm_sq_to_K, countableKet_norm]
  norm_num

theorem fourParticle_identity_pairLift_energy :
    (inner ℂ (⟨countableKet (Finset.range 4), by simpa using countableKet_sector (Finset.range 4)⟩ : countableSector 4)
      (countablePairLift 4 1 ⟨countableKet (Finset.range 4),
        by simpa using countableKet_sector (Finset.range 4)⟩)).re = 6 := by
  rw [countablePairLift_gram, countablePairAmplify_one]
  change (inner ℂ (countablePairStack 4 _) (countablePairStack 4 _)).re = _
  rw [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow]
  change ‖countablePairStack 4 _‖^2 = (6 : ℝ)
  exact fourParticle_pairStack_norm_sq

end VortexGap.Examples
