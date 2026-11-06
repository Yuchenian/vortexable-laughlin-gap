import VortexGap.Physical.PlaneFieldDerivative
import VortexGap.Fermion.CountableWedgeAnnihilation
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped ComplexOrder

theorem planeCoherent_wedge_tangent (z c : ℂ) :
    countableWedge (planeCoherent z) (planeCoherentTangent z c) =
      c • countableTwoFramePair (planeTwoFrame z) := by
  have h : countableWedge (planeBargmann z)
      (c • planeJet z - (inner ℝ z c : ℂ) • planeBargmann z) =
      c • countableWedge (planeBargmann z) (planeJet z) := by
    change countableWedgeRight (planeBargmann z) (_ - _) = _
    rw [map_sub, map_smul, map_smul]
    change c • countableWedge (planeBargmann z) (planeJet z) -
      (inner ℝ z c : ℂ) • countableWedge (planeBargmann z) (planeBargmann z) = _
    rw [countableWedge_self, smul_zero, sub_zero]
  rw [planeCoherent, planeCoherentTangent, countableWedge_smul_smul, h,
    planeTwoFramePair_jet, smul_smul, smul_smul]
  congr 1
  rw [← Complex.ofReal_mul, ← Real.exp_add]
  have he : -‖z‖^2/2 + -‖z‖^2/2 = -‖z‖^2 := by ring
  rw [he]
  ring

theorem planeEvaluation_wedge_tangent (ell : ℝ) (z c : ℂ) :
    countableWedge (planeEvaluation ell z) (planeEvaluationTangent ell z c) =
      ((((Real.sqrt (2*Real.pi*ell^2))⁻¹ : ℂ)^2)*
        (starRingEnd ℂ) (c / ((Real.sqrt 2*ell : ℝ) : ℂ))) •
      countableTwoFramePair (planeTwoFrame ((starRingEnd ℂ) (planeCoordinate ell z))) := by
  rw [planeEvaluation, planeEvaluationTangent, countableWedge_smul_smul,
    planeCoherent_wedge_tangent, smul_smul]
  congr 1
  ring

def planeContactCoefficient (ell : ℝ) (c : ℂ) : ℂ :=
  -((((Real.sqrt (2*Real.pi*ell^2))⁻¹ : ℂ)^2) * (c / ((Real.sqrt 2*ell : ℝ) : ℂ)))

/-- Actual directional contact amplitude on every completed finite-particle sector. -/
theorem planeFilteredField_contact_pair (R : CountableOrbital →L[ℂ] CountableOrbital)
    (hR : 0 ≤ R) (ell : ℝ) (z c : ℂ) (N : ℕ) (x : countableSector N) :
    (planeFilteredField R ell z * planeFilteredFieldDerivative R ell z c) x =
      planeContactCoefficient ell c • countablePairAnnihilate N
        (countablePairFilter R hR (countableTwoFramePair
          (planeTwoFrame ((starRingEnd ℂ) (planeCoordinate ell z))))) x := by
  have hw := congrArg (countablePairFilter R hR) (planeEvaluation_wedge_tangent ell z c)
  rw [countablePairFilter_wedge, map_smul] at hw
  rw [planeFilteredField, planeFilteredFieldDerivative, countableAnnihilate_anticommute]
  change -(countableAnnihilate (R (planeEvaluationTangent ell z c))
    (countableAnnihilate (R (planeEvaluation ell z)) x)) = _
  rw [← countablePairAnnihilate_wedge, hw, countablePairAnnihilate_smul]
  simp only [planeContactCoefficient, smul_apply, map_mul, map_pow, map_inv₀,
    Complex.conj_ofReal, starRingEnd_self_apply, neg_smul]

theorem planeContactCoefficient_norm_sq (ell : ℝ) (hell : 0 < ell) (c : ℂ) :
    ‖planeContactCoefficient ell c‖^2 = ‖c‖^2/(8*Real.pi^2*ell^6) := by
  have ha : (Real.sqrt (2*Real.pi*ell^2))^2 = 2*Real.pi*ell^2 := Real.sq_sqrt (by positivity)
  have hb : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  simp only [planeContactCoefficient, norm_neg, norm_mul, norm_pow, norm_div, norm_inv,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    abs_of_pos hell, mul_pow, div_pow, inv_pow]
  rw [ha, hb]
  field_simp
  ring

theorem planeContactCoefficient_xy_normalization (ell : ℝ) (hell : 0 < ell) :
    4*Real.pi*ell^4*(‖planeContactCoefficient ell 1‖^2+‖planeContactCoefficient ell Complex.I‖^2) =
      1/(Real.pi*ell^2) := by
  rw [planeContactCoefficient_norm_sq ell hell, planeContactCoefficient_norm_sq ell hell]
  norm_num
  field_simp
  ring

theorem planeFilteredField_xy_energy (R : CountableOrbital →L[ℂ] CountableOrbital)
    (hR : 0 ≤ R) (ell : ℝ) (hell : 0 < ell) (z : ℂ) (N : ℕ) (x : countableSector N) :
    4*Real.pi*ell^4 *
      (‖(planeFilteredField R ell z * planeFilteredFieldDerivative R ell z 1) x‖^2 +
       ‖(planeFilteredField R ell z * planeFilteredFieldDerivative R ell z Complex.I) x‖^2) =
      (1/(Real.pi*ell^2))*‖countablePairAnnihilate N
        (countablePairFilter R hR (countableTwoFramePair
          (planeTwoFrame ((starRingEnd ℂ) (planeCoordinate ell z))))) x‖^2 := by
  simp_rw [planeFilteredField_contact_pair R hR, norm_smul, mul_pow]
  have h := congrArg (fun s : ℝ => s * ‖countablePairAnnihilate N
    (countablePairFilter R hR (countableTwoFramePair
      (planeTwoFrame ((starRingEnd ℂ) (planeCoordinate ell z))))) x‖^2)
    (planeContactCoefficient_xy_normalization ell hell)
  simpa only [mul_add, add_mul, mul_assoc] using h

end VortexGap.Fermion





