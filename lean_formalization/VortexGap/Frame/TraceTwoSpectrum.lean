import VortexGap.Frame.TraceTwo
import Mathlib.Analysis.InnerProductSpace.Trace
noncomputable section
set_option autoImplicit false
namespace VortexGap.Frame

theorem singularValues_two_sq_sum (K : Module.End ℂ TwoSpace) :
    K.singularValues 0 ^ 2 + K.singularValues 1 ^ 2 =
      ((K.adjoint.comp K).trace ℂ TwoSpace).re := by
  have hn : Module.finrank ℂ TwoSpace = 2 := by simp [TwoSpace]
  rw [← RCLike.re_eq_complex_re, K.isSymmetric_adjoint_comp_self.re_trace_eq_sum_eigenvalues hn, Fin.sum_univ_two]
  exact congrArg₂ (fun x y : ℝ => x+y)
    (K.sq_singularValues_fin hn 0) (K.sq_singularValues_fin hn 1)

theorem two_adjoint_det (K : Module.End ℂ TwoSpace) :
    K.adjoint.det = (starRingEnd ℂ) K.det := by
  let b := EuclideanSpace.basisFun (Fin 2) ℂ
  rw [← LinearMap.det_toMatrix b.toBasis K.adjoint, LinearMap.toMatrix_adjoint,
    Matrix.det_conjTranspose, LinearMap.det_toMatrix]
  rfl

theorem singularValues_two_prod (K : Module.End ℂ TwoSpace) :
    K.singularValues 0 * K.singularValues 1 = ‖K.det‖ := by
  have hn : Module.finrank ℂ TwoSpace = 2 := by simp [TwoSpace]
  have hd := K.isSymmetric_adjoint_comp_self.det_eq_prod_eigenvalues hn
  simp only [Fin.prod_univ_two] at hd
  rw [← K.sq_singularValues_fin hn 0, ← K.sq_singularValues_fin hn 1] at hd
  have he := congrArg norm hd
  simp only [LinearMap.det_comp, two_adjoint_det, norm_mul, RCLike.norm_conj,
    RCLike.norm_ofReal, abs_pow, sq_abs] at he
  apply (sq_eq_sq₀ (mul_nonneg (K.singularValues_nonneg 0) (K.singularValues_nonneg 1))
    (norm_nonneg _)).mp
  rw [mul_pow, pow_two ‖K.det‖]
  exact he.symm

theorem traceNormTwo_sq_trace_det (K : Module.End ℂ TwoSpace) :
    traceNormTwo K ^ 2 = ((K.adjoint.comp K).trace ℂ TwoSpace).re + 2*‖K.det‖ := by
  rw [← singularValues_two_sq_sum, ← singularValues_two_prod, traceNormTwo]
  ring

def twoOperatorMatrix (K : Module.End ℂ TwoSpace) : Matrix (Fin 2) (Fin 2) ℂ :=
  LinearMap.toMatrix (EuclideanSpace.basisFun (Fin 2) ℂ).toBasis
    (EuclideanSpace.basisFun (Fin 2) ℂ).toBasis K

theorem twoOperatorMatrix_entry (K : Module.End ℂ TwoSpace) (i j : Fin 2) :
    twoOperatorMatrix K i j = K (PiLp.single 2 j 1) i := by
  simp [twoOperatorMatrix, LinearMap.toMatrix_apply, OrthonormalBasis.repr_apply_apply,
    EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left]

theorem twoOperatorMatrix_det (K : Module.End ℂ TwoSpace) :
    (twoOperatorMatrix K).det = K.det := LinearMap.det_toMatrix _ _

theorem two_gram_trace (K : Module.End ℂ TwoSpace) :
    ((K.adjoint.comp K).trace ℂ TwoSpace).re =
      ∑ i : Fin 2, ∑ j : Fin 2, ‖twoOperatorMatrix K i j‖^2 := by
  rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin 2) ℂ), Complex.re_sum]
  simp only [LinearMap.comp_apply, LinearMap.adjoint_inner_right]
  simp_rw [← RCLike.re_eq_complex_re, ← norm_sq_eq_re_inner (𝕜 := ℂ),
    EuclideanSpace.norm_sq_eq, EuclideanSpace.basisFun_apply, twoOperatorMatrix_entry]
  exact Finset.sum_comm

theorem traceNormTwo_sq_matrix (K : Module.End ℂ TwoSpace) :
    traceNormTwo K ^ 2 =
      (∑ i : Fin 2, ∑ j : Fin 2, ‖twoOperatorMatrix K i j‖^2) +
        2*‖(twoOperatorMatrix K).det‖ := by
  rw [traceNormTwo_sq_trace_det, two_gram_trace, twoOperatorMatrix_det]

end VortexGap.Frame




