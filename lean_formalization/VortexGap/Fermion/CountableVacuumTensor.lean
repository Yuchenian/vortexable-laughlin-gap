import VortexGap.Fermion.CountableOrbitalPullback
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped ENNReal

/-- Actual environment vacuum tensor a system state in completed l2 coordinates. -/
def countableVacuumTensor : CountableSpace →L[ℂ] CountableSplitSpace :=
  (l2Curry (Finset ℕ) (Finset ℕ)).symm.toLinearIsometry.toContinuousLinearMap.comp
    (lp.singleContinuousLinearMap ℂ (fun _ : Finset ℕ => CountableSpace) 2 ∅)

theorem countableVacuumTensor_coordinate (x : CountableSpace) (A B : Finset ℕ) :
    countableVacuumTensor x (A,B) = if A = ∅ then x B else 0 := by
  change (lp.single 2 ∅ x : L2Matrix (Finset ℕ) (Finset ℕ)) A B = _
  by_cases h : A = ∅
  · subst A
    simp [lp.single_apply]
  · simp [lp.single_apply, h, Ne.symm h]

theorem countableVacuumTensor_norm (x : CountableSpace) :
    ‖countableVacuumTensor x‖ = ‖x‖ := by
  change ‖(l2Curry (Finset ℕ) (Finset ℕ)).symm (lp.single 2 ∅ x)‖ = _
  rw [(l2Curry (Finset ℕ) (Finset ℕ)).symm.norm_map,
    lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]

theorem countableVacuumTensor_ket (B : Finset ℕ) :
    countableVacuumTensor (countableKet B) = countableSplitKet (∅,B) := by
  apply (l2Curry (Finset ℕ) (Finset ℕ)).injective
  change (l2Curry (Finset ℕ) (Finset ℕ))
    ((l2Curry (Finset ℕ) (Finset ℕ)).symm (lp.single 2 ∅ (countableKet B))) = _
  rw [(l2Curry (Finset ℕ) (Finset ℕ)).apply_symm_apply]
  change lp.single 2 ∅ (lp.single 2 B 1) =
    l2Curry (Finset ℕ) (Finset ℕ) (lp.single 2 (∅,B) 1)
  rw [l2Curry_single]

theorem countableFockSplit_system (x : CountableSpace) :
    countableFockSplit (countableFockIsometry countableSysOrbital x) = countableVacuumTensor x := by
  let L : CountableSpace →L[ℂ] CountableSplitSpace :=
    countableFockSplit.toLinearIsometry.toContinuousLinearMap.comp
      (countableFockIsometry countableSysOrbital).toContinuousLinearMap
  have h : L = countableVacuumTensor := by
    apply countableSpace_clm_ext
    intro B
    change countableFockSplit (countableFockIsometry countableSysOrbital (countableKet B)) = _
    rw [countableFockIsometry_ket, countableVacuumTensor_ket]
    have hf : (fun j => countableSysOrbital (orbitalKet j)) = countableSysBasis :=
      funext countableSysOrbital_ket
    rw [hf]
    have hi : countableJoinImage (∅,B) = countableOccupationImage countableSysBasis B := by
      rw [countableJoinImage_product, countableOccupationOperator_empty]
    rw [← hi, countableFockSplit_image]
  exact congrArg (fun T : CountableSpace →L[ℂ] CountableSplitSpace => T x) h

theorem countableVacuumTensor_environment (x : CountableSpace) :
    countableVacuumTensor x ∈ countableEnvironmentSector 0 := by
  intro AB hAB
  rw [countableVacuumTensor_coordinate]
  have h : AB.1 ≠ ∅ := by intro he; apply hAB; simp [he]
  simp only [h, ite_false]

theorem countableVacuumTensor_sector {N : ℕ} {x : CountableSpace}
    (hx : x ∈ countableSector N) : countableVacuumTensor x ∈ countableSplitSector N := by
  rw [← countableFockSplit_system]
  exact countableFockSplit_sector (countableFockIsometry_sector countableSysOrbital hx)
end VortexGap.Fermion
