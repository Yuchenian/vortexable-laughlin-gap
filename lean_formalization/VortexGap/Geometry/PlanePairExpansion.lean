import VortexGap.Geometry.PlanePairAmplitude
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped InnerProduct ENNReal

/-- Isometric synthesis into the actual closed span of the angular block vectors. -/
def planeBlockSynthesis : CountableOrbital →ₗᵢ[ℂ] CountablePairSpace :=
  planeBlockVector_orthonormal.orthogonalFamily.linearIsometry

theorem planeBlockSynthesis_hasSum (v : CountableOrbital) :
    HasSum (fun n => v n • planeBlockVector (n+1)) (planeBlockSynthesis v) := by
  simpa only [LinearIsometry.toSpanSingleton_apply, planeBlockSynthesis] using
    planeBlockVector_orthonormal.orthogonalFamily.hasSum_linearIsometry v

theorem planeBlockSynthesis_coordinate (v : CountableOrbital) (a : CountablePairIndex) :
    planeBlockSynthesis v a = v (a.val.1+a.val.2-1)*
      (planeBlockCoefficient (a.val.1+a.val.2) a.val.1 : ℂ) := by
  have hn : 0 < a.val.1+a.val.2 := by have := a.property; omega
  have hs := (planeBlockSynthesis_hasSum v).map
    (lp.evalCLM ℂ (fun _ : CountablePairIndex => ℂ) 2 a).toAddMonoidHom
    (lp.evalCLM ℂ (fun _ : CountablePairIndex => ℂ) 2 a).continuous
  change HasSum (fun n => v n * planeBlockVector (n+1) a) (planeBlockSynthesis v a) at hs
  rw [← hs.tsum_eq]
  rw [tsum_eq_single (a.val.1+a.val.2-1)]
  · have he : a.val.1+a.val.2-1+1 = a.val.1+a.val.2 := by omega
    rw [he, planeBlockVector_coordinate, ite_eq_left rfl]
  · intro n hne
    have he : a.val.1+a.val.2 ≠ n+1 := by omega
    rw [planeBlockVector_off_block _ _ he, mul_zero]

def planePairAmplitudes (z : ℂ) : CountableOrbital :=
  ⟨fun n => planePairAmplitude z (n+1), by
    apply memℓp_gen
    simpa only [show (2 : ℝ≥0∞).toReal = (2 : ℝ) by norm_num, Real.rpow_two] using
      (planePairAmplitude_hasSum_norm_sq z).summable⟩

/-- Equality in the completed pair Hilbert space, verified on every occupation
coordinate; no completeness of the block family in the entire pair space is assumed. -/
theorem planeBlockSynthesis_amplitudes (z : ℂ) :
    planeBlockSynthesis (planePairAmplitudes z) = countableTwoFramePair (planeTwoFrame z) := by
  ext a
  rw [planeBlockSynthesis_coordinate]
  change planePairAmplitude z (a.val.1+a.val.2-1+1)*
    (planeBlockCoefficient (a.val.1+a.val.2) a.val.1 : ℂ) = _
  have hn : a.val.1+a.val.2-1+1 = a.val.1+a.val.2 := by have := a.property; omega
  rw [hn, planeTwoFramePair_block_coordinate, planeBlockVector_coordinate, ite_eq_left rfl]

/-- Full Hilbert-norm angular block expansion of the actual coherent pair. -/
theorem planeTwoFramePair_hasSum_blocks (z : ℂ) :
    HasSum (fun n => planePairAmplitude z (n+1) • planeBlockVector (n+1))
      (countableTwoFramePair (planeTwoFrame z)) := by
  have h := planeBlockSynthesis_hasSum (planePairAmplitudes z)
  rw [planeBlockSynthesis_amplitudes] at h
  exact h

end VortexGap.Fermion
