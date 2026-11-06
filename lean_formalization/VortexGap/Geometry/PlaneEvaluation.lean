import VortexGap.Geometry.PlaneCoherent
import VortexGap.Fermion.CountableOrbitalActions
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped InnerProduct ComplexConjugate

/-- Dimensionless planar coordinate at magnetic length ell. -/
def planeCoordinate (ell : ℝ) (z : ℂ) : ℂ := z / ((Real.sqrt 2 * ell : ℝ) : ℂ)

/-- The standard Gaussian LLL orbital in physical coordinates, in factored normalization. -/
def planeWavefunction (ell : ℝ) (z : ℂ) (n : ℕ) : ℂ :=
  ((Real.sqrt (2*Real.pi*ell^2))⁻¹ : ℂ) *
    (Real.exp (-‖planeCoordinate ell z‖^2/2) : ℂ) *
      planeBargmannCoeff (planeCoordinate ell z) n

/-- The Riesz evaluation vector uses the conjugate coordinate, because annihilation
is antilinear. Its coordinates are the conjugates of the explicit LLL orbitals. -/
def planeEvaluation (ell : ℝ) (z : ℂ) : CountableOrbital :=
  ((Real.sqrt (2*Real.pi*ell^2))⁻¹ : ℂ) •
    planeCoherent (conj (planeCoordinate ell z))

def planeField (ell : ℝ) (z : ℂ) : CountableSpace →L[ℂ] CountableSpace :=
  countableAnnihilate (planeEvaluation ell z)

theorem planeEvaluation_coefficient (ell : ℝ) (z : ℂ) (n : ℕ) :
    planeEvaluation ell z n = conj (planeWavefunction ell z n) := by
  change ((Real.sqrt (2*Real.pi*ell^2))⁻¹ : ℂ) *
    ((Real.exp (-‖conj (planeCoordinate ell z)‖^2/2) : ℂ) *
      planeBargmannCoeff (conj (planeCoordinate ell z)) n) = _
  simp only [planeWavefunction, planeBargmannCoeff, map_mul, map_div₀,
    map_pow, map_inv₀, Complex.conj_ofReal, Complex.norm_conj]
  ring

theorem planeEvaluation_norm_sq (ell : ℝ) (hell : 0 < ell) (z : ℂ) :
    ‖planeEvaluation ell z‖^2 = 1 / (2*Real.pi*ell^2) := by
  rw [planeEvaluation, norm_smul, mul_pow, planeCoherent_norm_sq, mul_one]
  simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), inv_pow]
  rw [Real.sq_sqrt (by positivity), one_div]

theorem planeField_single_orbital (ell : ℝ) (z : ℂ) (n : ℕ) :
    planeField ell z (countableCreate (orbitalKet n) (countableKet ∅)) =
      planeWavefunction ell z n • countableKet ∅ := by
  rw [planeField, countableAnnihilate_create_vacuum]
  have hi : inner ℂ (planeEvaluation ell z) (orbitalKet n) = planeWavefunction ell z n := by
    rw [← inner_conj_symm, orbitalKet_inner_left, planeEvaluation_coefficient]
    simp
  rw [hi]

/-- Evaluation of every completed orbital is an actually convergent series of
standard LLL wavefunctions, not just a formula on finite orbital combinations. -/
theorem planeEvaluation_hasSum (ell : ℝ) (z : ℂ) (v : CountableOrbital) :
    HasSum (fun n => planeWavefunction ell z n * v n)
      (inner ℂ (planeEvaluation ell z) v) := by
  simpa only [RCLike.inner_apply', planeEvaluation_coefficient,
    starRingEnd_self_apply] using lp.hasSum_inner (𝕜 := ℂ) (planeEvaluation ell z) v

theorem planeEvaluation_ne_zero (ell : ℝ) (hell : 0 < ell) (z : ℂ) :
    planeEvaluation ell z ≠ 0 := by
  intro h
  have hh := planeEvaluation_norm_sq ell hell z
  rw [h] at hh
  have hp : 0 < 1/(2*Real.pi*ell^2) := by positivity
  norm_num at hh
  linarith

end VortexGap.Fermion
