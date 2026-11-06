import VortexGap.Operator.L2Amplification
import VortexGap.Fermion.CountableSplitOrbitals
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion

theorem countableSplit_create_sys_fiber (j : ℕ) (x : CountableSplitSpace) (A : Finset ℕ) :
    l2ProductFiber (countableSplitConjugate (countableCreate (countableSysBasis j)) x) A =
      ((-1 : ℂ)^A.card) • countableCreateMode j (l2ProductFiber x A) := by
  ext B
  change countableSplitConjugate (countableCreate (countableSysBasis j)) x (A,B) =
    ((-1 : ℂ)^A.card) * (countableCreateMode j (l2ProductFiber x A)) B
  rw [countableSplit_create_sys_coordinate, countableTransition_apply]
  by_cases h : j ∈ B
  · simp [h, countableFlip_of_mem h, l2ProductFiber_apply, mul_assoc]
  · simp [h]

theorem countableSplit_annihilate_sys_fiber (j : ℕ) (x : CountableSplitSpace) (A : Finset ℕ) :
    l2ProductFiber (countableSplitConjugate (countableAnnihilate (countableSysBasis j)) x) A =
      ((-1 : ℂ)^A.card) • countableAnnihilateMode j (l2ProductFiber x A) := by
  ext B
  change countableSplitConjugate (countableAnnihilate (countableSysBasis j)) x (A,B) =
    ((-1 : ℂ)^A.card) * (countableAnnihilateMode j (l2ProductFiber x A)) B
  rw [countableSplit_annihilate_sys_coordinate, countableTransition_apply]
  by_cases h : j ∈ B
  · simp [h]
  · simp [h, countableFlip_of_not_mem h, l2ProductFiber_apply, mul_assoc]
end VortexGap.Fermion
