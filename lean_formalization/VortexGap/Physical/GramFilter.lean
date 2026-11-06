import VortexGap.Physical.GramOrthogonalization
noncomputable section
set_option autoImplicit false
namespace VortexGap
open scoped InnerProduct ComplexOrder
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem inverse_real_smul_one (g : ℝ) (hg : 0 < g) :
    Ring.inverse (g • (1 : H →L[ℂ] H)) = g⁻¹ • (1 : H →L[ℂ] H) := by
  have hu : IsUnit (g • (1 : H →L[ℂ] H)) :=
    (IsStrictlyPositive.smul hg isStrictlyPositive_one).isUnit
  have hm : (g • (1 : H →L[ℂ] H)) * (g⁻¹ • 1) = 1 := by
    simp [smul_smul, ne_of_gt hg]
  calc
    Ring.inverse (g • (1 : H →L[ℂ] H)) = Ring.inverse (g • (1 : H →L[ℂ] H)) * 1 := (mul_one _).symm
    _ = Ring.inverse (g • (1 : H →L[ℂ] H)) * ((g • 1) * (g⁻¹ • 1)) := by rw [hm]
    _ = g⁻¹ • 1 := by rw [← mul_assoc, Ring.inverse_mul_cancel _ hu, one_mul]

def gramFilter (G : H →L[ℂ] H) (g : ℝ) : H →L[ℂ] H :=
  Real.sqrt g • CFC.sqrt (Ring.inverse G)

theorem gramFilter_nonneg (G : H →L[ℂ] H) (g : ℝ) : 0 ≤ gramFilter G g :=
  smul_nonneg (Real.sqrt_nonneg _) (CFC.sqrt_nonneg _)

theorem gramFilter_square (G : H →L[ℂ] H) (hG : IsStrictlyPositive G)
    (g : ℝ) (hg : 0 ≤ g) : (gramFilter G g)^2 = g • Ring.inverse G := by
  rw [gramFilter, pow_two, smul_mul_assoc, mul_smul_comm, smul_smul,
    ← pow_two (Real.sqrt g), Real.sq_sqrt hg, CFC.sqrt_mul_sqrt_self _ hG.ringInverse.nonneg]

theorem gramFilter_square_le_one (G : H →L[ℂ] H) (g : ℝ) (hg : 0 < g)
    (hlo : g • (1 : H →L[ℂ] H) ≤ G) : (gramFilter G g)^2 ≤ 1 := by
  have hs := IsStrictlyPositive.smul hg (isStrictlyPositive_one (A := H →L[ℂ] H))
  have hG := hs.of_le hlo
  have hi := CStarAlgebra.ringInverse_le_ringInverse hlo hs
  rw [inverse_real_smul_one g hg] at hi
  have hh := smul_le_smul_of_nonneg_left hi hg.le
  rw [gramFilter_square G hG g hg.le]
  simpa [smul_smul, ne_of_gt hg] using hh

theorem gramFilter_contraction (G : H →L[ℂ] H) (g : ℝ) (hg : 0 < g)
    (hlo : g • (1 : H →L[ℂ] H) ≤ G) : ‖gramFilter G g‖ ≤ 1 := by
  have hM := gramFilter_nonneg G g
  have hs : IsSelfAdjoint (gramFilter G g) := IsSelfAdjoint.of_nonneg hM
  have hsq : 0 ≤ (gramFilter G g)^2 := by cfc_tac
  have hn : ‖(gramFilter G g)^2‖ ≤ 1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg _ hsq).mpr (gramFilter_square_le_one G g hg hlo)
  rw [pow_two, hs.norm_mul_self] at hn
  exact (sq_le_one_iff₀ (norm_nonneg _)).mp hn

theorem gramFilter_square_lower (G : H →L[ℂ] H) (g u : ℝ) (hg : 0 < g) (hu : 0 < u)
    (hlo : g • (1 : H →L[ℂ] H) ≤ G) (hhi : G ≤ u • (1 : H →L[ℂ] H)) :
    (g/u) • (1 : H →L[ℂ] H) ≤ (gramFilter G g)^2 := by
  have hG := (IsStrictlyPositive.smul hg (isStrictlyPositive_one (A := H →L[ℂ] H))).of_le hlo
  have hi := CStarAlgebra.ringInverse_le_ringInverse hhi hG
  rw [inverse_real_smul_one u hu] at hi
  have hh := smul_le_smul_of_nonneg_left hi hg.le
  rw [gramFilter_square G hG g hg.le]
  simpa [smul_smul, div_eq_mul_inv] using hh

/-- The actual operator-norm loss is bounded by the Gram condition-number bound.
The scalar ordering is explicit, also making the statement valid on the zero Hilbert space. -/
theorem gramFilter_loss_le (G : H →L[ℂ] H) (g u : ℝ) (hg : 0 < g) (hgu : g ≤ u)
    (hlo : g • (1 : H →L[ℂ] H) ≤ G) (hhi : G ≤ u • (1 : H →L[ℂ] H)) :
    ‖1-(gramFilter G g)^2‖ ≤ 1-g/u := by
  have hu : 0 < u := hg.trans_le hgu
  have hd : 0 ≤ 1-g/u := sub_nonneg.mpr ((div_le_one hu).mpr hgu)
  have hpos : 0 ≤ 1-(gramFilter G g)^2 := sub_nonneg.mpr (gramFilter_square_le_one G g hg hlo)
  apply (CStarAlgebra.norm_le_iff_le_algebraMap _ hd hpos).mpr
  rw [Algebra.algebraMap_eq_smul_one]
  calc
    1-(gramFilter G g)^2 ≤ 1-(g/u) • (1 : H →L[ℂ] H) :=
      sub_le_sub_left (gramFilter_square_lower G g u hg hu hlo hhi) 1
    _ = (1-g/u) • (1 : H →L[ℂ] H) := by rw [sub_smul, one_smul]

theorem gram_filter_bounds {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (F : H →L[ℂ] K) (g u : ℝ) (hg : 0 < g) (hgu : g ≤ u)
    (hlo : g • (1 : H →L[ℂ] H) ≤ gramOperator F)
    (hhi : gramOperator F ≤ u • (1 : H →L[ℂ] H)) :
    0 ≤ gramFilter (gramOperator F) g ∧ ‖gramFilter (gramOperator F) g‖ ≤ 1 ∧
    ‖1-(gramFilter (gramOperator F) g)^2‖ ≤ 1-g/u :=
  ⟨gramFilter_nonneg _ _, gramFilter_contraction _ _ hg hlo, gramFilter_loss_le _ _ _ hg hgu hlo hhi⟩

theorem gramFilter_eq_normalized_inverse {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] (F : H →L[ℂ] K) (g : ℝ) :
    gramFilter (gramOperator F) g = Real.sqrt g • gramInvSqrt F := by
  rw [gramInvSqrt_eq_sqrt_inverse]
  rfl

end VortexGap
