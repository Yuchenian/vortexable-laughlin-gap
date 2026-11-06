import VortexGap.Physical.PlaneContactPair
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped ComplexOrder

/-- Independently defined derivative-contact field along a physical spatial direction. -/
def planeScalarContactField (R : CountableOrbital →L[ℂ] CountableOrbital)
    (ell : ℝ) (f : ℂ → ℂ) (z c : ℂ) : CountableSpace →L[ℂ] CountableSpace :=
  (f z • planeFilteredField R ell z) *
    deriv (fun t : ℝ => f (z+(t : ℂ)*c) • planeFilteredField R ell (z+(t : ℂ)*c)) 0

/-- Physical x/y derivative-contact density, with the original 4*pi*ell^4 coefficient. -/
def planeScalarContactDensity (R : CountableOrbital →L[ℂ] CountableOrbital)
    (ell : ℝ) (f : ℂ → ℂ) (z : ℂ) (N : ℕ) (x : countableSector N) : ℝ :=
  4*Real.pi*ell^4*(‖planeScalarContactField R ell f z 1 x‖^2 +
    ‖planeScalarContactField R ell f z Complex.I x‖^2)

theorem planeScalarContactField_cancel (R : CountableOrbital →L[ℂ] CountableOrbital)
    (ell : ℝ) (f : ℂ → ℂ) (z c : ℂ) (hf : DifferentiableAt ℝ f z) :
    planeScalarContactField R ell f z c =
      (f z)^2 • (planeFilteredField R ell z * planeFilteredFieldDerivative R ell z c) := by
  have hp : HasDerivAt (fun t : ℝ => z+(t : ℂ)*c) c 0 := by
    simpa using (Complex.ofRealCLM.hasDerivAt.mul_const c).const_add z
  have hf' : DifferentiableAt ℝ f (z+((0 : ℝ) : ℂ)*c) := by simpa using hf
  have hd := hf'.hasFDerivAt.comp_hasDerivAt 0 hp
  simpa only [planeScalarContactField, Complex.ofReal_zero, zero_mul, add_zero] using
    planeFilteredField_contact_cancel R ell z c (fun t : ℝ => f (z+(t : ℂ)*c)) _ hd

/-- The |f|^4 weight and physical normalization follow from actual derivatives and CAR. -/
theorem planeScalarContactDensity_pair (R : CountableOrbital →L[ℂ] CountableOrbital)
    (hR : 0 ≤ R) (ell : ℝ) (hell : 0 < ell) (f : ℂ → ℂ) (z : ℂ)
    (hf : DifferentiableAt ℝ f z) (N : ℕ) (x : countableSector N) :
    planeScalarContactDensity R ell f z N x =
      ‖f z‖^4 * (1/(Real.pi*ell^2))*‖countablePairAnnihilate N
        (countablePairFilter R hR (countableTwoFramePair
          (planeTwoFrame ((starRingEnd ℂ) (planeCoordinate ell z))))) x‖^2 := by
  simp only [planeScalarContactDensity, planeScalarContactField_cancel R ell f z _ hf,
    smul_apply, norm_smul, norm_pow, mul_pow]
  linear_combination (‖f z‖^4) * planeFilteredField_xy_energy R hR ell hell z N x

end VortexGap.Fermion
