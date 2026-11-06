import VortexGap.Geometry.SphereBloch
import VortexGap.Geometry.SpinorChart
import VortexGap.Geometry.BlochArea
import Mathlib.Topology.Homeomorph.Lemmas

noncomputable section
namespace VortexGap.Fermion
open OAI.Laughlin.Rotation

theorem sphereBlochConfiguration_injective (N : ℕ) :
    Function.Injective (@sphereBlochConfiguration N) := by
  intro x y
  induction x using Quot.ind with | _ g =>
  induction y using Quot.ind with | _ h =>
  intro he
  have one (i : Fin N) := spinor_rotation_phase (g i) (h i)
    (congrArg (fun p : BlochSphere => p.val.2) (congrFun he i))
    (congrArg (fun p : BlochSphere => p.val.1) (congrFun he i))
  choose z hz hh using one
  exact Quot.sound ⟨z,hz,funext hh⟩

def sphereConfigurationHomeomorph (N : ℕ) :
    spherePhaseQuotient N ≃ₜ (Fin N → BlochSphere) := by
  let e := Equiv.ofBijective _ ⟨sphereBlochConfiguration_injective N,sphereBlochConfiguration_surjective N⟩
  apply Continuous.homeoOfEquivCompactToT2 (f := e)
  exact continuous_quot_lift _ (continuous_pi fun i => sphereBloch_continuous.comp (continuous_apply i))

theorem sphereConfigurationHomeomorph_lift {N : ℕ} (g : Fin N → SourceSU2) :
    sphereConfigurationHomeomorph N (Quot.mk _ g) = fun i => sphereBloch (g i) := rfl

open VortexGap.Geometry MeasureTheory
/-- Actual finite-flux orbital product measure on the Euclidean sphere configurations. -/
theorem sphereOrbital_round_configuration (q N : ℕ) :
    MeasurePreserving (fun (g : Fin N → SourceSU2) i => roundBloch (g i))
      (Measure.pi (fun _ => sphereOrbitalMeasure q))
      (Measure.pi (fun _ => ENNReal.ofReal ((q:ℝ)+1) • normalizedRoundArea)) := by
  let : IsFiniteMeasure (ENNReal.ofReal ((q:ℝ)+1) • normalizedRoundArea) := ⟨by
    simp [Measure.smul_apply,ENNReal.ofReal_lt_top]⟩
  apply measurePreserving_pi
  intro i
  refine ⟨roundBloch_continuous.measurable,?_⟩
  rw [sphereOrbitalMeasure,Measure.map_smul,sphereBloch_round_area]
  exact roundBloch_continuous.measurable.aemeasurable

end VortexGap.Fermion
end
