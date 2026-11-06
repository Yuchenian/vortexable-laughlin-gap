import VortexGap.Geometry.PlaneMeasurability
import VortexGap.Geometry.PlaneEvaluation
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Complex.RealDeriv
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion

theorem planeBargmann_hasDerivAt_curve (f : ℝ → ℂ) (c : ℂ) (x : ℝ)
    (hf : HasDerivAt f c x) :
    HasDerivAt (fun t => planeBargmann (f t)) (c • planeJet (f x)) x := by
  have h := ((planeBargmann_hasDerivAt (f x)).hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt x hf
  simpa only [Function.comp_def] using! h

def planeCoherentTangent (z c : ℂ) : CountableOrbital :=
  (Real.exp (-‖z‖^2/2) : ℂ) •
    (c • planeJet z - (inner ℝ z c : ℂ) • planeBargmann z)

theorem planeCoherent_hasDerivAt_curve (f : ℝ → ℂ) (c : ℂ) (x : ℝ)
    (hf : HasDerivAt f c x) :
    HasDerivAt (fun t => planeCoherent (f t)) (planeCoherentTangent (f x) c) x := by
  have hg := ((hf.norm_sq.neg.div_const 2).exp).ofReal_comp
  have hb := planeBargmann_hasDerivAt_curve f c x hf
  convert hg.fun_smul hb using 1
  · rfl
  · dsimp [planeCoherentTangent]
    module

theorem planeCoherentTangent_zero (z : ℂ) : planeCoherentTangent z 0 = 0 := by
  simp [planeCoherentTangent]

def planeEvaluationTangent (ell : ℝ) (z c : ℂ) : CountableOrbital :=
  ((Real.sqrt (2*Real.pi*ell^2))⁻¹ : ℂ) •
    planeCoherentTangent ((starRingEnd ℂ) (planeCoordinate ell z))
      ((starRingEnd ℂ) (c / ((Real.sqrt 2*ell : ℝ) : ℂ)))

theorem planeEvaluation_hasDerivAt_curve (ell : ℝ) (f : ℝ → ℂ) (c : ℂ) (x : ℝ)
    (hf : HasDerivAt f c x) :
    HasDerivAt (fun t => planeEvaluation ell (f t)) (planeEvaluationTangent ell (f x) c) x := by
  have hc : HasDerivAt (fun t => (starRingEnd ℂ) (planeCoordinate ell (f t)))
      ((starRingEnd ℂ) (c / ((Real.sqrt 2*ell : ℝ) : ℂ))) x := by
    simpa only [planeCoordinate, Complex.conjCLE_apply] using!
      Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt x
        (hf.div_const (((Real.sqrt 2*ell : ℝ) : ℂ)))
  exact (planeCoherent_hasDerivAt_curve _ _ _ hc).const_smul
    (((Real.sqrt (2*Real.pi*ell^2))⁻¹ : ℂ))

end VortexGap.Fermion


