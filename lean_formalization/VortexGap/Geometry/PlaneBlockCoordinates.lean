import VortexGap.Geometry.PlaneBlocks
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open Finset
open scoped InnerProduct

theorem planeBlockVector_at_index (n : ℕ) (i : planeBlockModes n) :
    planeBlockVector n (planeBlockIndex n i) = (planeBlockCoefficient n i.val : ℂ) := by
  simp only [planeBlockVector, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply]
  simp [lp.single_apply, Pi.single_apply, (planeBlockIndex_injective n).eq_iff]

theorem planeBlockVector_off_block (n : ℕ) (a : CountablePairIndex)
    (h : a.val.1+a.val.2 ≠ n) : planeBlockVector n a = 0 := by
  simp only [planeBlockVector, lp.coeFn_sum, lp.coeFn_smul, Finset.sum_apply, Pi.smul_apply]
  apply sum_eq_zero
  intro i _
  have he : a ≠ planeBlockIndex n i := by
    intro he
    apply h
    rw [he]
    exact planeBlockIndex_total n i
  rw [lp.single_apply_ne 2 _ _ he, smul_zero]

/-- The actual Hilbert vector has precisely the factorial block coordinates;
this also identifies its support without an assumed angular projection. -/
theorem planeBlockVector_coordinate (n : ℕ) (a : CountablePairIndex) :
    planeBlockVector n a =
      if a.val.1+a.val.2 = n then (planeBlockCoefficient n a.val.1 : ℂ) else 0 := by
  by_cases h : a.val.1+a.val.2 = n
  · rw [ite_eq_left h]
    let i : planeBlockModes n := ⟨a.val.1, by
      have hp := a.property
      simp only [planeBlockModes, mem_filter, mem_range]
      constructor <;> omega⟩
    have hi : planeBlockIndex n i = a := by
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · dsimp [planeBlockIndex, i]; omega
    rw [← hi, planeBlockVector_at_index]
    rfl
  · rw [ite_eq_right h]
    exact planeBlockVector_off_block n a h

theorem planeBlockVector_coordinate_norm_sq (n : ℕ) (a : CountablePairIndex)
    (h : a.val.1+a.val.2 = n) :
    ‖planeBlockVector n a‖^2 = (planeBlockCoefficient n a.val.1)^2 := by
  rw [planeBlockVector_coordinate, ite_eq_left h, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- A two-component nonzero block, checked in the actual completed pair vector. -/
theorem planeBlockVector_three_weights :
    ‖planeBlockVector 3 (⟨(0,3), by decide⟩ : CountablePairIndex)‖^2 = (3/4 : ℝ) ∧
    ‖planeBlockVector 3 (⟨(1,2), by decide⟩ : CountablePairIndex)‖^2 = (1/4 : ℝ) := by
  constructor <;> rw [planeBlockVector_coordinate_norm_sq _ _ (by rfl), planeBlockCoefficient_sq] <;>
    norm_num [Nat.choose]

end VortexGap.Fermion
