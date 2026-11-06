import VortexGap.Fermion.CountablePairAnnihilation
import VortexGap.Examples.CountableOrbitals

noncomputable section
set_option autoImplicit false
namespace VortexGap.Examples
open Fermion
open scoped InnerProduct ComplexConjugate

theorem geometricOneParticle_coefficient (j : ℕ) :
    geometricOneParticle {j} = geometricOrbital j := by
  have h := countableAnnihilate_create_vacuum (orbitalKet j) geometricOrbital
  rw [countableAnnihilate_ket, orbitalKet_inner_left] at h
  have hc := congrArg (fun x : CountableSpace => x ∅) h
  simpa [geometricOneParticle, countableAnnihilateMode, countableTransition_apply,
    countableSign, countableKet_apply] using hc

theorem geometricOneParticle_annihilate_zero :
    countableAnnihilate (orbitalKet 0) geometricOneParticle = countableKet ∅ := by
  rw [geometricOneParticle, countableAnnihilate_create_vacuum, orbitalKet_inner_left,
    geometricOrbital_coefficient]
  norm_num

/-- e_0 wedge v with v_j=(i/2)^j: a genuinely infinite-support pair state. -/
def geometricPairState : CountableSpace := countableCreate (orbitalKet 0) geometricOneParticle

theorem geometricPairState_sector : geometricPairState ∈ countableSector 2 :=
  countableCreate_sector _ geometricOneParticle_sector

theorem geometricPairState_norm_sq : ‖geometricPairState‖ ^ 2 = (1 / 3 : ℝ) := by
  have h := countableOrbital_norm_identity (orbitalKet 0) geometricOneParticle
  change ‖geometricPairState‖ ^ 2 +
    ‖countableAnnihilate (orbitalKet 0) geometricOneParticle‖ ^ 2 =
    ‖orbitalKet 0‖ ^ 2 * ‖geometricOneParticle‖ ^ 2 at h
  rw [geometricOneParticle_annihilate_zero, countableKet_norm, orbitalKet_norm,
    geometricOneParticle_norm_sq] at h
  nlinarith

def geometricPair : CountablePairSpace := countablePairCoordinates geometricPairState

theorem geometricPair_embedding : countablePairEmbedding geometricPair = geometricPairState :=
  countablePairEmbedding_coordinates geometricPairState_sector

theorem geometricPair_norm_sq : ‖geometricPair‖ ^ 2 = (1 / 3 : ℝ) := by
  rw [geometricPair, countablePairCoordinates_norm_on_sector geometricPairState_sector,
    geometricPairState_norm_sq]

theorem geometricPair_ne_zero : geometricPair ≠ 0 := by
  intro h
  have hn := geometricPair_norm_sq
  rw [h] at hn
  norm_num at hn

def geometricPairIndex (j : ℕ) : CountablePairIndex := ⟨(0, j + 1), by omega⟩

theorem geometricPairIndex_injective : Function.Injective geometricPairIndex := by
  intro i j h
  have hv := congrArg (fun a : CountablePairIndex => a.val.2) h
  change i + 1 = j + 1 at hv
  omega

theorem geometricPair_coefficient (j : ℕ) :
    geometricPair (geometricPairIndex j) = geometricOrbital (j + 1) := by
  rw [geometricPair, countablePairCoordinates_coefficient]
  change geometricPairState {0, j + 1} = _
  rw [geometricPairState, countableCreate_ket]
  change countableTransition 0 true geometricOneParticle {0, j + 1} = _
  simp [countableTransition_apply, countableSign, Finset.erase_insert,
    geometricOneParticle_coefficient]

theorem geometricPair_coefficient_ne_zero (j : ℕ) : geometricPair (geometricPairIndex j) ≠ 0 := by
  rw [geometricPair_coefficient]
  exact geometricOrbital_coefficient_ne_zero _

theorem geometricPair_infinite_support : Set.Infinite {a | geometricPair a ≠ 0} :=
  Set.infinite_of_injective_forall_mem geometricPairIndex_injective geometricPair_coefficient_ne_zero

theorem geometricPair_imaginary_annihilation :
    countablePairAnnihilate 2 (Complex.I • geometricPair)
        ⟨geometricPairState, geometricPairState_sector⟩ =
      ((-1 / 3 : ℂ) * Complex.I) • countableKet ∅ := by
  have hx : (⟨geometricPairState, geometricPairState_sector⟩ : countableSector 2) =
      ⟨countablePairEmbedding geometricPair, countablePairEmbedding_sector geometricPair⟩ :=
    Subtype.ext geometricPair_embedding.symm
  have hi : inner ℂ geometricPair geometricPair = (1 / 3 : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, geometricPair_norm_sq]
    norm_num
  rw [hx, countablePairAnnihilate_pairEmbedding, inner_smul_left, hi]
  congr 1
  norm_num <;> ring

theorem fourParticle_pairStack_norm_sq :
    ‖countablePairStack 4 ⟨countableKet (Finset.range 4),
      by simpa using countableKet_sector (Finset.range 4)⟩‖ ^ 2 = (6 : ℝ) := by
  change ‖countablePairStackLinear 4 _‖ ^ 2 = _
  rw [countablePairStackLinear_norm_sq]
  norm_num [countableKet_norm, Nat.choose]

end VortexGap.Examples

