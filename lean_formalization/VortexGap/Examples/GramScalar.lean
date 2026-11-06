import VortexGap.Physical.GramFilter
noncomputable section
set_option autoImplicit false
namespace VortexGap.Examples
open scoped ComplexOrder
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem gramScalar_square :
    (gramFilter ((4 : ℝ) • (1 : H →L[ℂ] H)) 1)^2 = (1/4 : ℝ) • (1 : H →L[ℂ] H) := by
  have hs : IsStrictlyPositive ((4 : ℝ) • (1 : H →L[ℂ] H)) :=
    IsStrictlyPositive.smul (by norm_num) isStrictlyPositive_one
  rw [gramFilter_square _ hs 1 (by norm_num), one_smul, inverse_real_smul_one 4 (by norm_num)]
  norm_num

theorem gramScalar_loss [Nontrivial H] :
    ‖(1 : H →L[ℂ] H)-(gramFilter ((4 : ℝ) • (1 : H →L[ℂ] H)) 1)^2‖ = (3/4 : ℝ) := by
  rw [gramScalar_square (H := H)]
  have he : (1 : H →L[ℂ] H)-(1/4 : ℝ) • 1 = (3/4 : ℝ) • 1 := by module
  rw [he, norm_smul]
  norm_num

theorem gramScalar_not_identity [Nontrivial H] :
    gramFilter ((4 : ℝ) • (1 : H →L[ℂ] H)) 1 ≠ 1 := by
  intro h
  have hδ := gramScalar_loss (H := H)
  rw [h] at hδ
  norm_num at hδ

/-- A deliberately loose upper bound gives a strictly conservative loss bound.
This is an operator-interface regression, not a spatial band-deformation example. -/
theorem gramScalar_strict_bound [Nontrivial H] :
    ‖(1 : H →L[ℂ] H)-(gramFilter ((4 : ℝ) • (1 : H →L[ℂ] H)) 1)^2‖ < 1-(1:ℝ)/8 := by
  rw [gramScalar_loss (H := H)]
  norm_num

theorem gramScalar_certificate :
    ‖(1 : H →L[ℂ] H)-(gramFilter ((4 : ℝ) • (1 : H →L[ℂ] H)) 1)^2‖ ≤ (7/8 : ℝ) := by
  have hlo : (1 : ℝ) • (1 : H →L[ℂ] H) ≤ (4 : ℝ) • (1 : H →L[ℂ] H) :=
    smul_le_smul_of_nonneg_right (by norm_num) zero_le_one
  have hhi : (4 : ℝ) • (1 : H →L[ℂ] H) ≤ (8 : ℝ) • (1 : H →L[ℂ] H) :=
    smul_le_smul_of_nonneg_right (by norm_num) zero_le_one
  have h := gramFilter_loss_le ((4 : ℝ) • (1 : H →L[ℂ] H)) 1 8
    (by norm_num) (by norm_num) hlo hhi
  norm_num at h ⊢
  exact h

end VortexGap.Examples

