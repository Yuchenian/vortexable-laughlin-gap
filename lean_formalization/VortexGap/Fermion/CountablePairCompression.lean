import VortexGap.Fermion.CountableVacuumLoss
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped InnerProduct ComplexOrder

theorem countablePairMap_adjoint_wedge (J : CountableOrbital →ₗᵢ[ℂ] CountableOrbital)
    (u v : CountableOrbital) :
    (countablePairMap J).adjoint (countableWedge u v) =
      countableWedge (J.toContinuousLinearMap.adjoint u) (J.toContinuousLinearMap.adjoint v) := by
  ext a
  have h := ContinuousLinearMap.adjoint_inner_right (countablePairMap J)
    (countableWedge (orbitalKet a.val.1) (orbitalKet a.val.2)) (countableWedge u v)
  rw [countableWedge_map, countableWedge_inner] at h
  rw [countableWedge_basis, lp.inner_single_left] at h
  simp only [RCLike.inner_apply, map_one, mul_one] at h
  rw [h, countableWedge_coordinate]
  have hi (j : ℕ) (w : CountableOrbital) :
      inner ℂ (J (orbitalKet j)) w = (J.toContinuousLinearMap.adjoint w) j := by
    rw [← orbitalKet_inner_left, ContinuousLinearMap.adjoint_inner_right]
    rfl
  rw [hi, hi, hi, hi]

/-- Exterior square of a positive contraction, constructed by the actual loss dilation. -/
def countablePairCompression (M : CountableOrbital →L[ℂ] CountableOrbital)
    (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1) : CountablePairSpace →L[ℂ] CountablePairSpace :=
  (countablePairMap countableSysOrbital).adjoint.comp
    (countablePairMap (countableLossEmbedding M hM hc))

theorem countablePairCompression_wedge (M : CountableOrbital →L[ℂ] CountableOrbital)
    (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1) (u v : CountableOrbital) :
    countablePairCompression M hM hc (countableWedge u v) = countableWedge (M u) (M v) := by
  rw [countablePairCompression, ContinuousLinearMap.comp_apply, countableWedge_map,
    countablePairMap_adjoint_wedge, countableSysOrbital_adjoint_loss,
    countableSysOrbital_adjoint_loss]

theorem countablePairCompression_norm_le (M : CountableOrbital →L[ℂ] CountableOrbital)
    (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1) : ‖countablePairCompression M hM hc‖ ≤ 1 := by
  have h1 : ‖(countablePairMap countableSysOrbital).adjoint‖ ≤ 1 := by
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact (countablePairIsometry countableSysOrbital).norm_toContinuousLinearMap_le
  have h2 : ‖countablePairMap (countableLossEmbedding M hM hc)‖ ≤ 1 :=
    (countablePairIsometry (countableLossEmbedding M hM hc)).norm_toContinuousLinearMap_le
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1))
theorem countableNormalized_nonneg
    (M : CountableOrbital →L[ℂ] CountableOrbital) (hM : 0 ≤ M) :
    0 ≤ ((‖M‖⁻¹ : ℝ) : ℂ) • M := by
  apply ContinuousLinearMap.nonneg_iff_isPositive.mpr
  exact (ContinuousLinearMap.nonneg_iff_isPositive.mp hM).smul_of_nonneg
    (Complex.zero_le_real.mpr (inv_nonneg.mpr (norm_nonneg M)))

theorem countableNormalized_contract
    (M : CountableOrbital →L[ℂ] CountableOrbital) (h : ‖M‖ ≠ 0) :
    ‖((‖M‖⁻¹ : ℝ) : ℂ) • M‖ ≤ 1 := by
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg M)), inv_mul_cancel₀ h]

/-- Bounded exterior square of a positive operator, constructed by normalized loss
dilation. The zero case is handled explicitly. -/
def countablePairFilter (M : CountableOrbital →L[ℂ] CountableOrbital) (hM : 0 ≤ M) :
    CountablePairSpace →L[ℂ] CountablePairSpace :=
  if h : ‖M‖ = 0 then 0 else
    ((‖M‖^2 : ℝ) : ℂ) • countablePairCompression (((‖M‖⁻¹ : ℝ) : ℂ) • M)
      (countableNormalized_nonneg M hM) (countableNormalized_contract M h)

theorem countableWedge_smul_smul (a b : ℂ) (u v : CountableOrbital) :
    countableWedge (a • u) (b • v) = (a*b) • countableWedge u v := by
  change countableWedgeLeft (b • v) (a • u) = _
  rw [map_smul]
  change a • countableWedgeRight u (b • v) = _
  rw [map_smul, smul_smul]
  rfl

theorem countablePairFilter_wedge
    (M : CountableOrbital →L[ℂ] CountableOrbital) (hM : 0 ≤ M)
    (u v : CountableOrbital) :
    countablePairFilter M hM (countableWedge u v) = countableWedge (M u) (M v) := by
  by_cases h : ‖M‖ = 0
  · have hz : M = 0 := norm_eq_zero.mp h
    simp [countablePairFilter, h, hz, countableWedge]
  · rw [countablePairFilter, dif_neg h, smul_apply, countablePairCompression_wedge]
    simp only [smul_apply, countableWedge_smul_smul, smul_smul]
    have hs : ((‖M‖^2 : ℝ) : ℂ) *
        (((‖M‖⁻¹ : ℝ) : ℂ) * ((‖M‖⁻¹ : ℝ) : ℂ)) = 1 := by
      have he : ‖M‖^2 * (‖M‖⁻¹ * ‖M‖⁻¹) = 1 := by field_simp
      exact_mod_cast he
    rw [hs, one_smul]

theorem countablePairFilter_norm_le
    (M : CountableOrbital →L[ℂ] CountableOrbital) (hM : 0 ≤ M) :
    ‖countablePairFilter M hM‖ ≤ ‖M‖^2 := by
  by_cases h : ‖M‖ = 0
  · simp [countablePairFilter, h]
  · rw [countablePairFilter, dif_neg h, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg _)]
    exact (mul_le_mul_of_nonneg_left (countablePairCompression_norm_le _ _ _) (sq_nonneg _)).trans_eq
      (mul_one _)
end VortexGap.Fermion
