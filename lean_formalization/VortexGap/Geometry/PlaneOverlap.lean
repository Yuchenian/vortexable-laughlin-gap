import VortexGap.Geometry.PlaneTwoFrame
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open VortexGap.Frame

theorem planeTwoFrame_overlap_00 (z w : ℂ) :
    countableTwoFrameOverlap (planeTwoFrame z) (planeTwoFrame w) (PiLp.single 2 0 1) 0 =
      inner ℂ (planeCoherent z) (planeCoherent w) := by
  rw [countableTwoFrameOverlap_entry, planeTwoFrame_first, planeTwoFrame_first]

theorem planeTwoFrame_overlap_01 (z w : ℂ) :
    countableTwoFrameOverlap (planeTwoFrame z) (planeTwoFrame w) (PiLp.single 2 1 1) 0 =
      ((starRingEnd ℂ) z-(starRingEnd ℂ) w)*inner ℂ (planeCoherent z) (planeCoherent w) := by
  rw [countableTwoFrameOverlap_entry, planeTwoFrame_first, planeTwoFrame_second,
    planeCoherent_inner_excited]

theorem planeTwoFrame_overlap_10 (z w : ℂ) :
    countableTwoFrameOverlap (planeTwoFrame z) (planeTwoFrame w) (PiLp.single 2 0 1) 1 =
      (w-z)*inner ℂ (planeCoherent z) (planeCoherent w) := by
  rw [countableTwoFrameOverlap_entry, planeTwoFrame_second, planeTwoFrame_first,
    planeExcited_inner_coherent]

theorem planeTwoFrame_overlap_11 (z w : ℂ) :
    countableTwoFrameOverlap (planeTwoFrame z) (planeTwoFrame w) (PiLp.single 2 1 1) 1 =
      (1+(w-z)*((starRingEnd ℂ) z-(starRingEnd ℂ) w))*
        inner ℂ (planeCoherent z) (planeCoherent w) := by
  rw [countableTwoFrameOverlap_entry, planeTwoFrame_second, planeTwoFrame_second,
    planeExcited_inner_excited]

theorem planeCoherent_overlap_norm (z w : ℂ) :
    ‖inner ℂ (planeCoherent z) (planeCoherent w)‖ = Real.exp (-‖w-z‖^2/2) := by
  rw [planeCoherent_inner]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), Complex.norm_exp, ← Real.exp_add]
  congr 1
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    Complex.sub_re, Complex.sub_im]
  ring

def planeOverlapMatrix (z w : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => countableTwoFrameOverlap (planeTwoFrame z) (planeTwoFrame w) (PiLp.single 2 j 1) i

theorem planeOverlapMatrix_det (z w : ℂ) :
    (planeOverlapMatrix z w).det = (inner ℂ (planeCoherent z) (planeCoherent w))^2 := by
  rw [Matrix.det_fin_two]
  simp only [planeOverlapMatrix, planeTwoFrame_overlap_00, planeTwoFrame_overlap_01,
    planeTwoFrame_overlap_10, planeTwoFrame_overlap_11]
  ring

theorem planeCoherent_overlap_norm_sq (z w : ℂ) :
    ‖inner ℂ (planeCoherent z) (planeCoherent w)‖^2 = Real.exp (-‖w-z‖^2) := by
  rw [planeCoherent_overlap_norm, pow_two, ← Real.exp_add]
  congr 1
  ring

theorem planeOverlapMatrix_det_norm (z w : ℂ) :
    ‖(planeOverlapMatrix z w).det‖ = Real.exp (-‖w-z‖^2) := by
  rw [planeOverlapMatrix_det, norm_pow, planeCoherent_overlap_norm_sq]

theorem planeOverlap_excited_factor (z w : ℂ) :
    1+(w-z)*((starRingEnd ℂ) z-(starRingEnd ℂ) w) = ((1-‖w-z‖^2 : ℝ) : ℂ) := by
  apply Complex.ext <;>
    simp [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.mul_im] <;> ring

theorem planeOverlapMatrix_frobenius_sq (z w : ℂ) :
    (∑ i : Fin 2, ∑ j : Fin 2, ‖planeOverlapMatrix z w i j‖^2) =
      Real.exp (-‖w-z‖^2) * ((‖w-z‖^2)^2+2) := by
  have hc : ‖(starRingEnd ℂ) z-(starRingEnd ℂ) w‖ = ‖w-z‖ := by
    rw [← map_sub, RCLike.norm_conj, norm_sub_rev]
  simp only [Fin.sum_univ_two, planeOverlapMatrix, planeTwoFrame_overlap_00,
    planeTwoFrame_overlap_01, planeTwoFrame_overlap_10, planeTwoFrame_overlap_11,
    planeOverlap_excited_factor, norm_mul, mul_pow, hc, planeCoherent_overlap_norm_sq,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]
  ring

end VortexGap.Fermion


