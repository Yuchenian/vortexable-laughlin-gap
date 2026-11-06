import VortexGap.Geometry.PlaneOverlap
import VortexGap.Frame.TraceTwoSpectrum
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open VortexGap.Frame

theorem planeOverlapMatrix_eq_operatorMatrix (z w : ℂ) :
    planeOverlapMatrix z w = twoOperatorMatrix (countableTwoFrameOverlap (planeTwoFrame z) (planeTwoFrame w)) := by
  ext i j
  exact (twoOperatorMatrix_entry _ i j).symm

theorem planeTwoFrame_traceNorm_sq (z w : ℂ) :
    traceNormTwo (countableTwoFrameOverlap (planeTwoFrame z) (planeTwoFrame w))^2 =
      Real.exp (-‖w-z‖^2)*((‖w-z‖^2)^2+4) := by
  rw [traceNormTwo_sq_matrix, ← planeOverlapMatrix_eq_operatorMatrix,
    planeOverlapMatrix_frobenius_sq, planeOverlapMatrix_det_norm]
  ring

theorem planeTwoFrame_traceNorm (z w : ℂ) :
    traceNormTwo (countableTwoFrameOverlap (planeTwoFrame z) (planeTwoFrame w)) =
      Real.exp (-‖w-z‖^2/2)*Real.sqrt ((‖w-z‖^2)^2+4) := by
  apply (sq_eq_sq₀ (traceNormTwo_nonneg _) (by positivity)).mp
  rw [planeTwoFrame_traceNorm_sq, mul_pow, Real.sq_sqrt (by positivity),
    pow_two (Real.exp _), ← Real.exp_add]
  congr 2
  ring

end VortexGap.Fermion
