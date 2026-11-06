import VortexGap.Geometry.PlaneTraceNorm
import VortexGap.Geometry.PlaneGaussian
import Mathlib.MeasureTheory.Group.Integral
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory VortexGap.Frame

def planeSchurKernel (z : ℂ) : ℝ :=
  Real.exp (-(1/2 : ℝ)*‖z‖^2)*Real.sqrt ((‖z‖^2)^2+4)

def planeSchurMajorant (z : ℂ) : ℝ :=
  (‖z‖^4+16)*Real.exp (-(1/2 : ℝ)*‖z‖^2)/(4*Real.sqrt 3)

theorem plane_sqrt_majorant (t : ℝ) :
    Real.sqrt (t^2+4) ≤ (t^2+16)/(4*Real.sqrt 3) := by
  rw [le_div_iff₀ (by positivity)]
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have ht := Real.sq_sqrt (show 0 ≤ t^2+4 by positivity)
  nlinarith [sq_nonneg (Real.sqrt (t^2+4)-2*Real.sqrt 3)]

theorem planeSchurKernel_nonneg (z : ℂ) : 0 ≤ planeSchurKernel z := by
  unfold planeSchurKernel
  positivity

theorem planeSchurKernel_le (z : ℂ) : planeSchurKernel z ≤ planeSchurMajorant z := by
  have h := mul_le_mul_of_nonneg_left (plane_sqrt_majorant (‖z‖^2))
    (Real.exp_pos (-(1/2 : ℝ)*‖z‖^2)).le
  dsimp [planeSchurKernel, planeSchurMajorant]
  convert h using 1
  ring

theorem planeSchurMajorant_integrable : Integrable planeSchurMajorant := by
  have h := ((plane_gaussian_moment_integrable (1/2) (by norm_num) 2).add
    ((plane_gaussian_moment_integrable (1/2) (by norm_num) 0).const_mul 16)).div_const (4*Real.sqrt 3)
  convert h using 1
  funext z
  dsimp [planeSchurMajorant]
  norm_num
  ring

theorem planeSchurKernel_integrable : Integrable planeSchurKernel := by
  apply planeSchurMajorant_integrable.mono' (by unfold planeSchurKernel; fun_prop)
  exact Filter.Eventually.of_forall (fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (planeSchurKernel_nonneg z)]
    exact planeSchurKernel_le z)

theorem planeSchurMajorant_integral :
    (∫ z : ℂ, planeSchurMajorant z) = 4*Real.pi*Real.sqrt 3 := by
  have he : planeSchurMajorant = fun z : ℂ =>
      ((‖z‖^(2*2)*Real.exp (-(1/2 : ℝ)*‖z‖^2))+
        16*(‖z‖^(2*0)*Real.exp (-(1/2 : ℝ)*‖z‖^2)))/(4*Real.sqrt 3) := by
    funext z
    dsimp [planeSchurMajorant]
    norm_num
    ring
  rw [he, integral_div, integral_add
    (plane_gaussian_moment_integrable (1/2) (by norm_num) 2)
    ((plane_gaussian_moment_integrable (1/2) (by norm_num) 0).const_mul 16), integral_const_mul,
    plane_gaussian_moment (1/2) (by norm_num) 2, plane_gaussian_moment (1/2) (by norm_num) 0]
  norm_num
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hn : Real.sqrt 3 ≠ 0 := by positivity
  field_simp
  nlinarith

theorem planeTwoFrame_traceNorm_kernel (z w : ℂ) :
    traceNormTwo (countableTwoFrameOverlap (planeTwoFrame z) (planeTwoFrame w)) =
      planeSchurKernel (w-z) := by
  rw [planeTwoFrame_traceNorm]
  unfold planeSchurKernel
  congr 2
  ring

theorem planeSchurKernel_integral_le :
    (∫ z : ℂ, planeSchurKernel z) ≤ 4*Real.pi*Real.sqrt 3 := by
  rw [← planeSchurMajorant_integral]
  exact integral_mono planeSchurKernel_integrable planeSchurMajorant_integrable planeSchurKernel_le

theorem planeTwoFrame_schur_integrable (z : ℂ) :
    Integrable (fun w => traceNormTwo (countableTwoFrameOverlap (planeTwoFrame z) (planeTwoFrame w)))
      planePairMeasure := by
  simp_rw [planeTwoFrame_traceNorm_kernel]
  exact (planeSchurKernel_integrable.comp_sub_right z).smul_measure ENNReal.ofReal_ne_top

theorem planeTwoFrame_schur_bound (z : ℂ) :
    (∫ w, traceNormTwo (countableTwoFrameOverlap (planeTwoFrame z) (planeTwoFrame w))
      ∂planePairMeasure) ≤ 8*Real.sqrt 3 := by
  simp_rw [planeTwoFrame_traceNorm_kernel]
  rw [planePairMeasure, integral_smul_measure, ENNReal.toReal_ofReal (by positivity),
    smul_eq_mul, integral_sub_right_eq_self]
  have h := mul_le_mul_of_nonneg_left planeSchurKernel_integral_le
    (show (0 : ℝ) ≤ 2/Real.pi by positivity)
  convert h using 1
  field_simp
  norm_num

theorem plane_schur_constant_lt_fourteen : 8*Real.sqrt 3 < (14 : ℝ) := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hn := Real.sqrt_nonneg (3 : ℝ)
  nlinarith

theorem planeTwoFrame_schur_fourteen (z : ℂ) :
    (∫ w, traceNormTwo (countableTwoFrameOverlap (planeTwoFrame z) (planeTwoFrame w))
      ∂planePairMeasure) ≤ 14 :=
  (planeTwoFrame_schur_bound z).trans plane_schur_constant_lt_fourteen.le

end VortexGap.Fermion



