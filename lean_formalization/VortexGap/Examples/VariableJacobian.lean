import VortexGap.Geometry.CoordinateChange
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import VortexGap.Physical.CoordinateContact
import VortexGap.Reference.CertifiedPlane

noncomputable section

namespace VortexGap.Fermion
open Filter

private def warpAxis (x : ℝ) := x + Real.sin x / 2

private theorem warpAxis_deriv (x : ℝ) : HasDerivAt warpAxis (1 + Real.cos x/2) x :=
  (hasDerivAt_id x).add ((Real.hasDerivAt_sin x).div_const 2)

private def warpAxisHomeo : ℝ ≃ₜ ℝ := by
  have hc : Continuous warpAxis := by unfold warpAxis; fun_prop
  have hm : StrictMono warpAxis := strictMono_of_deriv_pos (fun x => by
    rw [(warpAxis_deriv x).deriv]; linarith [Real.neg_one_le_cos x])
  have ht : Tendsto warpAxis atTop atTop := tendsto_atTop.2 (fun b => by
    filter_upwards [eventually_ge_atTop (b+1)] with x hx
    unfold warpAxis; linarith [Real.neg_one_le_sin x])
  have hb : Tendsto warpAxis atBot atBot := tendsto_atBot.2 (fun b => by
    filter_upwards [eventually_le_atBot (b-1)] with x hx
    unfold warpAxis; linarith [Real.sin_le_one x])
  exact (hm.orderIsoOfSurjective warpAxis (hc.surjective ht hb)).toHomeomorph

def variableJacobianMap : ℂ ≃ₜ ℂ :=
  let E := Complex.equivRealProdCLM.toHomeomorph
  E.trans ((warpAxisHomeo.prodCongr (Homeomorph.refl ℝ)).trans E.symm)

theorem variableJacobianMap_apply (z : ℂ) : variableJacobianMap z =
    z + ((Real.sin z.re/2 : ℝ) : ℂ) := by
  change (⟨warpAxis z.re,z.im⟩ : ℂ) = _
  apply Complex.ext <;> simp only [warpAxis,Complex.add_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,add_zero]

theorem variableJacobianMap_smooth : ContDiff ℝ 2 variableJacobianMap := by
  have he : (⇑variableJacobianMap) = _ := funext variableJacobianMap_apply
  rw [he]; apply contDiff_id.add; apply Complex.ofRealCLM.contDiff.comp; exact (Real.contDiff_sin.comp Complex.reCLM.contDiff).div_const 2

private theorem warp_derivative (z c : ℂ) : fderiv ℝ (⇑variableJacobianMap) z c =
    c + ((Real.cos z.re*c.re/2 : ℝ):ℂ) := by
  have he : (⇑variableJacobianMap) = _ := funext variableJacobianMap_apply
  have hs := Complex.ofRealCLM.hasFDerivAt.comp z
    ((((Real.hasDerivAt_sin z.re).div_const 2).hasFDerivAt).comp z Complex.reCLM.hasFDerivAt)
  have h := (hasFDerivAt_id (𝕜 := ℝ) z).add hs
  rw [he]
  change (fderiv ℝ (id + (Complex.ofRealCLM ∘ (fun s : ℝ => Real.sin s / 2) ∘ Complex.re)) z) c = _
  rw [h.fderiv]
  change c + (((c.re*(Real.cos z.re/2) : ℝ)):ℂ) = _
  congr 2; ring

theorem warped_jacobian (z : ℂ) : coordinateJacobian variableJacobianMap z = 1 + Real.cos z.re/2 := by
  rw [coordinateJacobian_axes,warp_derivative,warp_derivative]
  simp only [Complex.one_re,Complex.one_im,Complex.I_re,Complex.I_im,mul_one,mul_zero,zero_div,
    Complex.ofReal_zero,add_zero,Complex.add_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero]

theorem warped_weight (z : ℂ) : coordinateMetricWeight variableJacobianMap (variableJacobianMap z) =
    (1+Real.cos z.re/2)*((1+Real.cos z.re/2)^2+1)/2 := by
  simp only [coordinateMetricWeight,Homeomorph.symm_apply_apply,warped_jacobian,warp_derivative,
    Complex.one_re,Complex.I_re,mul_one,mul_zero,zero_div,Complex.ofReal_zero,add_zero,Complex.norm_I,one_pow]
  rw [← Complex.ofReal_one,← Complex.ofReal_add,Complex.norm_real,Real.norm_eq_abs,sq_abs]

theorem warped_weight_bounds (w : ℂ) : 5/16 ≤ coordinateMetricWeight variableJacobianMap w ∧
    coordinateMetricWeight variableJacobianMap w ≤ 39/16 := by
  obtain ⟨z,rfl⟩ := variableJacobianMap.surjective w
  rw [warped_weight]
  let j := 1+Real.cos z.re/2
  have hl : (1/2:ℝ) ≤ j := by dsimp [j]; linarith [Real.neg_one_le_cos z.re]
  have hu : j ≤ (3/2:ℝ) := by dsimp [j]; linarith [Real.cos_le_one z.re]
  change 5/16 ≤ j*(j^2+1)/2 ∧ j*(j^2+1)/2 ≤ 39/16
  constructor
  · nlinarith [mul_le_mul hl (add_le_add_right (pow_le_pow_left₀ (by norm_num) hl 2) 1) (by positivity) (by linarith : 0 ≤ j)]
  · nlinarith [mul_le_mul hu (add_le_add_right (pow_le_pow_left₀ (by linarith) hu 2) 1) (by positivity) (by norm_num : 0 ≤ (3/2:ℝ))]

end VortexGap.Fermion

namespace VortexGap.Fermion
open MeasureTheory

theorem warped_physical_old_gap (ell : ℝ) (hell : 0 < ell) (N : ℕ) :
    ∃ A : countableSector N →L[ℂ] countableSector N, A.IsPositive ∧
      (∀ x, (inner ℂ x (A x)).re = ∫ z, coordinateDensity variableJacobianMap ell z N x) ∧
      LinearMap.ker A.toLinearMap = LinearMap.ker (countablePairLift N planePairOperator).toLinearMap ∧
      ∀ s ∈ spectrum ℝ A, s = 0 ∨ 1/80 ≤ s := by
  have hp z : 0 < coordinateJacobian variableJacobianMap z := by
    rw [warped_jacobian]; linarith [Real.neg_one_le_cos z.re]
  have h := coordinatePhysical_kernel_gap variableJacobianMap variableJacobianMap_smooth hp
    (5/16) (39/16) (by norm_num) warped_weight_bounds ell hell N (1/25)
    (by simpa using countablePlane_old_bound N)
  norm_num only [show (5/16:ℝ)*(1/25)=1/80 by norm_num] at h
  exact h

end VortexGap.Fermion
