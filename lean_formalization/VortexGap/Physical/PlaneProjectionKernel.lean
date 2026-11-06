import VortexGap.Physical.PlaneCoordinateDomain
import VortexGap.Geometry.PlaneOverlap
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory Filter
open scoped InnerProduct ComplexConjugate
local notation "H" => Lp ℂ 2 (volume : Measure ℂ)

def planeLLLProjection (ell : ℝ) (hell : 0 < ell) : H →L[ℂ] H :=
  let J := (planeLLLEmbedding ell hell).toContinuousLinearMap
  J.comp J.adjoint

theorem planeLLLProjection_fixes (ell : ℝ) (hell : 0 < ell) (v : CountableOrbital) :
    planeLLLProjection ell hell (planeLLLEmbedding ell hell v) = planeLLLEmbedding ell hell v := by
  let J := (planeLLLEmbedding ell hell).toContinuousLinearMap
  have he : J.adjoint.comp J = 1 :=
    (ContinuousLinearMap.norm_map_iff_adjoint_comp_self J).mp (planeLLLEmbedding ell hell).norm_map
  exact congrArg (fun T : CountableOrbital →L[ℂ] CountableOrbital => J (T v)) he

def planeProjectionKernel (ell : ℝ) (z w : ℂ) : ℂ :=
  inner ℂ (planeEvaluation ell z) (planeEvaluation ell w)

theorem planeLLLProjection_integral (ell : ℝ) (hell : 0 < ell) (x : H) :
    planeLLLProjection ell hell x =ᵐ[volume] fun z => ∫ w, planeProjectionKernel ell z w * x w := by
  let J := (planeLLLEmbedding ell hell).toContinuousLinearMap
  filter_upwards [planeLLLEmbedding_coe ell hell (J.adjoint x)] with z hz
  change planeLLLEmbedding ell hell (J.adjoint x) z = _
  rw [hz, ContinuousLinearMap.adjoint_inner_right, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [planeLLLEmbedding_coe ell hell (planeEvaluation ell z)] with w hw
  change inner ℂ (planeLLLEmbedding ell hell (planeEvaluation ell z) w) (x w) = _
  rw [hw, RCLike.inner_apply', inner_conj_symm]
  rfl

theorem planeProjectionKernel_norm (ell : ℝ) (hell : 0 < ell) (z w : ℂ) :
    ‖planeProjectionKernel ell z w‖ =
      (2*Real.pi*ell^2)⁻¹ * Real.exp (-‖z-w‖^2/(4*ell^2)) := by
  simp only [planeProjectionKernel, planeEvaluation, inner_smul_left, inner_smul_right,
    norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), planeCoherent_overlap_norm, ← map_sub, Complex.norm_conj]
  rw [← mul_assoc, ← mul_inv_rev, ← sq, Real.sq_sqrt (by positivity)]
  congr 2
  rw [planeCoordinate, planeCoordinate, ← sub_div, norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by positivity), div_pow, mul_pow, Real.sq_sqrt (by norm_num),
    norm_sub_rev w z]
  field_simp; ring

private theorem coordinateGaussianMoment (ell : ℝ) (hell : 0 < ell) :
    (∫ u : ℂ, ‖u‖ * Real.exp (-‖u‖^2/(4*ell^2))) =
      4*Real.pi*ell^3*Real.sqrt Real.pi := by
  let b : ℝ := ((2*ell)^2)⁻¹
  have hb : 0 < b := by dsimp [b]; positivity
  have h := Complex.integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 1) (b := b)
    (by norm_num) (by norm_num) hb
  rw [show (-(1+2)/2 : ℝ) = -(3/2) by norm_num, Real.rpow_neg_eq_inv_rpow,
    show b⁻¹ = (2*ell)^2 by simp [b], Real.rpow_div_two_eq_sqrt _ (sq_nonneg _),
    Real.sqrt_sq (by positivity : 0 ≤ 2*ell), show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast, show ((1+2)/2 : ℝ) = 1/2+1 by norm_num,
    Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq] at h
  simp only [Real.rpow_one, Real.rpow_two] at h
  have he (u : ℂ) : -‖u‖^2/(4*ell^2) = -b*‖u‖^2 := by dsimp [b]; field_simp; ring
  simp_rw [he]
  rw [h]
  ring

/-- Both row and column integrals of the absolute commutator kernel have
the same value, uniformly over the physical point. -/
theorem planeCoordinateKernel_schur (ell : ℝ) (hell : 0 < ell) (z : ℂ) :
    (∫ w : ℂ, ‖(z-w) * planeProjectionKernel ell z w‖) = 2*Real.sqrt Real.pi*ell ∧
    (∫ w : ℂ, ‖(w-z) * planeProjectionKernel ell w z‖) = 2*Real.sqrt Real.pi*ell := by
  let k := fun u : ℂ => ‖u‖ * Real.exp (-‖u‖^2/(4*ell^2))
  have hi : (∫ w : ℂ, (2*Real.pi*ell^2)⁻¹ * k (w-z)) = 2*Real.sqrt Real.pi*ell := by
    rw [integral_const_mul, integral_sub_right_eq_self]
    change _ * (∫ u : ℂ, ‖u‖ * Real.exp (-‖u‖^2/(4*ell^2))) = _
    rw [coordinateGaussianMoment ell hell]
    field_simp; ring
  constructor <;> convert hi using 1 <;> apply integral_congr_ae <;> apply Eventually.of_forall <;>
    intro w <;> simp only [norm_mul, planeProjectionKernel_norm ell hell, k, norm_sub_rev z w] <;> ring

private theorem kernel_times_integrable (ell : ℝ) (hell : 0 < ell) (z : ℂ) (x : H) :
    Integrable (fun w => planeProjectionKernel ell z w * x w) := by
  have hi := MeasureTheory.L2.integrable_inner (𝕜 := ℂ) (planeLLLEmbedding ell hell (planeEvaluation ell z)) x
  apply hi.congr
  filter_upwards [planeLLLEmbedding_coe ell hell (planeEvaluation ell z)] with w hw
  rw [hw, RCLike.inner_apply', inner_conj_symm]
  rfl

theorem planeCoordinate_commutator_integral (ell : ℝ) (hell : 0 < ell) (x : planeCoordinateDomain) :
    ∀ᵐ z ∂volume, z * planeLLLProjection ell hell x z -
      planeLLLProjection ell hell (planeCoordinateMul x) z =
      ∫ w, (z-w) * planeProjectionKernel ell z w * x.val w := by
  filter_upwards [planeLLLProjection_integral ell hell x,
    planeLLLProjection_integral ell hell (planeCoordinateMul x)] with z hx hy
  rw [hx, hy, ← integral_const_mul, ← integral_sub ((kernel_times_integrable ell hell z x).const_mul z)
    (kernel_times_integrable ell hell z (planeCoordinateMul x))]
  apply integral_congr_ae
  filter_upwards [planeCoordinateMul_coe x] with w hw
  change z * (planeProjectionKernel ell z w * x.val w) -
    planeProjectionKernel ell z w * planeCoordinateMul x w = _
  rw [hw]
  ring

end VortexGap.Fermion
