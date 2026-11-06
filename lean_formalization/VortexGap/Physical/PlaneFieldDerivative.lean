import VortexGap.Geometry.PlaneRealDerivative
import VortexGap.Physical.ContactCancellation
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion

/-- The actual antilinear annihilation map is real-linear for real-coordinate calculus. -/
def countableAnnihilateReal : CountableOrbital →L[ℝ] (CountableSpace →L[ℂ] CountableSpace) :=
  ({ toFun := countableAnnihilate
     map_add' := countableAnnihilate_add
     map_smul' := fun r v => by
       simpa only [RCLike.real_smul_eq_coe_smul (K := ℂ), Complex.conj_ofReal, RingHom.id_apply] using!
         countableAnnihilate_smul (r : ℂ) v } : CountableOrbital →ₗ[ℝ] _).mkContinuous 1
    (fun v => by
      change ‖countableAnnihilate v‖ ≤ 1*‖v‖
      simpa only [one_mul] using countableAnnihilate_opNorm_le v)

theorem countableAnnihilate_hasDerivAt (f : ℝ → CountableOrbital) (v : CountableOrbital) (x : ℝ)
    (hf : HasDerivAt f v x) :
    HasDerivAt (fun t => countableAnnihilate (f t)) (countableAnnihilate v) x :=
  countableAnnihilateReal.hasFDerivAt.comp_hasDerivAt x hf

def planeFilteredField (R : CountableOrbital →L[ℂ] CountableOrbital) (ell : ℝ) (z : ℂ) :
    CountableSpace →L[ℂ] CountableSpace := countableAnnihilate (R (planeEvaluation ell z))

def planeFilteredFieldDerivative (R : CountableOrbital →L[ℂ] CountableOrbital)
    (ell : ℝ) (z c : ℂ) : CountableSpace →L[ℂ] CountableSpace :=
  countableAnnihilate (R (planeEvaluationTangent ell z c))

theorem planeFilteredField_hasDerivAt_curve (R : CountableOrbital →L[ℂ] CountableOrbital)
    (ell : ℝ) (f : ℝ → ℂ) (c : ℂ) (x : ℝ) (hf : HasDerivAt f c x) :
    HasDerivAt (fun t => planeFilteredField R ell (f t))
      (planeFilteredFieldDerivative R ell (f x) c) x := by
  exact countableAnnihilate_hasDerivAt _ _ x
    ((R.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt x (planeEvaluation_hasDerivAt_curve ell f c x hf))

theorem planeFilteredField_hasDerivAt_direction (R : CountableOrbital →L[ℂ] CountableOrbital)
    (ell : ℝ) (z c : ℂ) :
    HasDerivAt (fun t : ℝ => planeFilteredField R ell (z+(t : ℂ)*c))
      (planeFilteredFieldDerivative R ell z c) 0 := by
  have hf : HasDerivAt (fun t : ℝ => z+(t : ℂ)*c) c 0 := by
    simpa using (Complex.ofRealCLM.hasDerivAt.mul_const c).const_add z
  simpa only [Complex.ofReal_zero, zero_mul, add_zero] using
    planeFilteredField_hasDerivAt_curve R ell _ c 0 hf

theorem planeFilteredField_contact_cancel (R : CountableOrbital →L[ℂ] CountableOrbital)
    (ell : ℝ) (z c : ℂ) (f : ℝ → ℂ) (df : ℂ) (hf : HasDerivAt f df 0) :
    (f 0 • planeFilteredField R ell z) *
        deriv (fun t : ℝ => f t • planeFilteredField R ell (z+(t : ℂ)*c)) 0 =
      (f 0)^2 • (planeFilteredField R ell z * planeFilteredFieldDerivative R ell z c) := by
  have h := differentiable_contact_cancel (fun t : ℝ => planeFilteredField R ell (z+(t : ℂ)*c))
    (planeFilteredFieldDerivative R ell z c) f df 0 (R (planeEvaluation ell z))
    (planeFilteredField_hasDerivAt_direction R ell z c) hf (by simp [planeFilteredField])
  simpa only [Complex.ofReal_zero, zero_mul, add_zero] using h

end VortexGap.Fermion



