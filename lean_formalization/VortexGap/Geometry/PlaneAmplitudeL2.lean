import VortexGap.Geometry.PlaneRotation
import VortexGap.Geometry.PlanePairExpansion
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory

/-- Actual L2 equivalence class of each positive angular amplitude. -/
def planeAmplitudeL2 (n : ℕ) : Lp ℂ 2 planePairMeasure :=
  (planePairAmplitude_memLp n).toLp (fun z => planePairAmplitude z (n+1))

theorem planeAmplitudeL2_coe (n : ℕ) :
    planeAmplitudeL2 n =ᵐ[planePairMeasure] (fun z => planePairAmplitude z (n+1)) :=
  (planePairAmplitude_memLp n).coeFn_toLp

theorem planeAmplitudeL2_inner (m n : ℕ) :
    inner ℂ (planeAmplitudeL2 m) (planeAmplitudeL2 n) = if m=n then 1 else 0 := by
  rw [L2.inner_def]
  calc
    (∫ z, inner ℂ (planeAmplitudeL2 m z) (planeAmplitudeL2 n z) ∂planePairMeasure) =
        ∫ z, inner ℂ (planePairAmplitude z (m+1))
          (planePairAmplitude z (n+1)) ∂planePairMeasure := by
      apply integral_congr_ae
      filter_upwards [planeAmplitudeL2_coe m, planeAmplitudeL2_coe n] with z hm hn
      rw [hm, hn]
    _ = _ := planePairAmplitude_integral_inner m n

theorem planeAmplitudeL2_orthonormal : Orthonormal ℂ planeAmplitudeL2 :=
  orthonormal_iff_ite.mpr planeAmplitudeL2_inner

/-- Synthesis into position L2, constructed from the proved orthonormal family. -/
def planeAmplitudeSynthesis : CountableOrbital →ₗᵢ[ℂ] Lp ℂ 2 planePairMeasure :=
  planeAmplitudeL2_orthonormal.orthogonalFamily.linearIsometry

theorem planeAmplitudeSynthesis_hasSum (v : CountableOrbital) :
    HasSum (fun n => v n • planeAmplitudeL2 n) (planeAmplitudeSynthesis v) := by
  simpa only [LinearIsometry.toSpanSingleton_apply, planeAmplitudeSynthesis] using
    planeAmplitudeL2_orthonormal.orthogonalFamily.hasSum_linearIsometry v

theorem planeAmplitudeSynthesis_norm (v : CountableOrbital) :
    ‖planeAmplitudeSynthesis v‖ = ‖v‖ := planeAmplitudeSynthesis.norm_map v

end VortexGap.Fermion
