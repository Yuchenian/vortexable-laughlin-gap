import VortexGap.Geometry.PlaneBessel
import Mathlib.Analysis.Complex.CauchyIntegral
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory

theorem planeBargmann_continuous : Continuous planeBargmann :=
  continuous_iff_continuousAt.mpr (fun z => (planeBargmann_hasDerivAt z).continuousAt)

theorem planeJet_continuous : Continuous planeJet := by
  have hd : Differentiable ℂ planeBargmann := fun z => (planeBargmann_hasDerivAt z).differentiableAt
  have he : deriv planeBargmann = planeJet := funext (fun z => (planeBargmann_hasDerivAt z).deriv)
  rw [← he]
  exact hd.contDiff.continuous_deriv (by norm_num : (1 : WithTop ℕ∞) ≤ ⊤)

theorem planeCoherent_continuous : Continuous planeCoherent := by
  unfold planeCoherent
  exact (by fun_prop : Continuous (fun z : ℂ => (Real.exp (-‖z‖^2/2) : ℂ))).smul
    planeBargmann_continuous

theorem planeExcited_continuous : Continuous planeExcited := by
  unfold planeExcited
  exact (by fun_prop : Continuous (fun z : ℂ => (Real.exp (-‖z‖^2/2) : ℂ))).smul
    (planeJet_continuous.sub (Complex.continuous_conj.smul planeBargmann_continuous))

theorem planeTwoFrame_first_aestronglyMeasurable :
    AEStronglyMeasurable (fun z => planeTwoFrame z (PiLp.single 2 0 1)) planePairMeasure := by
  simp_rw [planeTwoFrame_first]
  exact planeCoherent_continuous.aestronglyMeasurable

theorem planeTwoFrame_second_aestronglyMeasurable :
    AEStronglyMeasurable (fun z => planeTwoFrame z (PiLp.single 2 1 1)) planePairMeasure := by
  simp_rw [planeTwoFrame_second]
  exact planeExcited_continuous.aestronglyMeasurable

theorem planeTwoFramePair_spanning_memLp (n : ℕ) :
    MemLp (fun z => countableTwoFramePair (planeTwoFrame z)) 2
      (planePairMeasure.restrict (spanningSets planePairMeasure n)) :=
  countableTwoFramePair_spanning_memLp planePairMeasure planeTwoFrame
    planeTwoFrame_first_aestronglyMeasurable planeTwoFrame_second_aestronglyMeasurable n

end VortexGap.Fermion
