import VortexGap.Fermion.CountablePairCompression
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped InnerProduct ENNReal ComplexOrder

theorem countablePairFilter_adjoint_wedge
    (M : CountableOrbital →L[ℂ] CountableOrbital) (hM : 0 ≤ M)
    (u v : CountableOrbital) :
    (countablePairFilter M hM).adjoint (countableWedge u v) =
      countableWedge (M u) (M v) := by
  ext a
  have h := ContinuousLinearMap.adjoint_inner_right (countablePairFilter M hM)
    (countableWedge (orbitalKet a.val.1) (orbitalKet a.val.2)) (countableWedge u v)
  rw [countablePairFilter_wedge, countableWedge_inner] at h
  rw [countableWedge_basis, lp.inner_single_left] at h
  simp only [RCLike.inner_apply, map_one, mul_one] at h
  rw [h, countableWedge_coordinate]
  have hi (j : ℕ) (w : CountableOrbital) :
      inner ℂ (M (orbitalKet j)) w = (M w) j := by
    exact ((ContinuousLinearMap.nonneg_iff_isPositive.mp hM).inner_left_eq_inner_right
      (orbitalKet j) w).trans (orbitalKet_inner_left j (M w))
  rw [hi, hi, hi, hi]

theorem countablePairFilter_adjoint
    (M : CountableOrbital →L[ℂ] CountableOrbital) (hM : 0 ≤ M) :
    (countablePairFilter M hM).adjoint = countablePairFilter M hM := by
  apply ContinuousLinearMap.ext
  intro p
  have hp : HasSum (fun a => p a • lp.single 2 a 1) p := by
    simpa only [← lp.single_smul, smul_eq_mul, mul_one]
      using lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) p
  have hs := hp.map (countablePairFilter M hM).adjoint.toAddMonoidHom
    (countablePairFilter M hM).adjoint.continuous
  have ht := hp.map (countablePairFilter M hM).toAddMonoidHom
    (countablePairFilter M hM).continuous
  have he (a : CountablePairIndex) :
      (countablePairFilter M hM).adjoint (lp.single 2 a 1) =
        countablePairFilter M hM (lp.single 2 a 1) := by
    rw [← countableWedge_basis a, countablePairFilter_adjoint_wedge, countablePairFilter_wedge]
  change HasSum (fun a => (countablePairFilter M hM).adjoint (p a • lp.single 2 a 1))
    ((countablePairFilter M hM).adjoint p) at hs
  change HasSum (fun a => countablePairFilter M hM (p a • lp.single 2 a 1))
    (countablePairFilter M hM p) at ht
  simp only [map_smul, he] at hs
  simp only [map_smul] at ht
  exact hs.unique ht
end VortexGap.Fermion