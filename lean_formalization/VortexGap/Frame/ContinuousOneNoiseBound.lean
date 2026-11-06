import VortexGap.Frame.ContinuousOneNoise

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory VortexGap.Frame
open scoped InnerProduct ENNReal ComplexOrder

variable {n : ℕ}
  (M : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
  {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
  (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1) (U : α → TwoFrame n)
  (hU0 : AEStronglyMeasurable (fun a => U a (PiLp.single 2 0 1)) μ)
  (hU1 : AEStronglyMeasurable (fun a => U a (PiLp.single 2 1 1)) μ)
  (ω : α → ℝ) (hω : ∀ a, 0 < ω a) (hωm : AEStronglyMeasurable ω μ)
  (C : ℝ)
  (hrowInt : ∀ᵐ a ∂μ, Integrable (fun b => traceNormTwo (twoFrameOverlap (U a) (U b)) * ω b) μ)
  (hrow : ∀ᵐ a ∂μ, (∫ b, traceNormTwo (twoFrameOverlap (U a) (U b)) * ω b ∂μ) ≤ C * ω a)

include hM hc hU0 hU1 hω hωm hrowInt hrow in
/-- Actual continuous-label CAR X1 estimate from raw, integrable trace-norm rows. -/
theorem continuousOneLossNoise_relative (x : Space n) :
    ‖continuousOneLossNoise M μ (fun a => U a (PiLp.single 2 0 1))
      (fun a => U a (PiLp.single 2 1 1)) x‖^2 ≤
      C * ‖1 - M^2‖ * (inner ℂ x (continuousFrameHamiltonian μ
        (fun a => exteriorSquare M.toLinearMap
          (wedgePair (U a (PiLp.single 2 0 1)) (U a (PiLp.single 2 1 1)))) x)).re := by
  let u := fun a => U a (PiLp.single 2 0 1)
  let v := fun a => U a (PiLp.single 2 1 1)
  let hun := fun a => (twoFrameColumn_norm (U a) 0).le
  let hvn := fun a => (twoFrameColumn_norm (U a) 1).le
  let hp := filteredPair_memLp M μ _ (wedgePair_memLp μ u v hU0 hU1 hun hvn)
  let z := continuousFrameAnalysis μ (fun a => exteriorSquare M.toLinearMap (wedgePair (u a) (v a))) hp x
  let r := continuousOneFrameSynthesis M μ u v hU0 hU1 hun hvn z
  rw [continuousOneLossNoise_factorization M μ u v hU0 hU1 hun hvn, orbitalEnvironmentEmbed_norm_sq]
  change ‖orbitalAmplify (lossDefect M) r‖^2 ≤ _
  have ha := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
    (orbitalAmplify_norm_le (lossDefect M) r)
  rw [mul_pow] at ha
  have hs : ‖r‖^2 ≤ C * ‖z‖^2 :=
    continuousOneFrameSynthesis_norm_sq_le M μ hc U hU0 hU1 ω hω hωm C hrowInt hrow z
  have hz := continuousFrameAnalysis_energy μ _ hp x
  change ‖z‖^2 = _ at hz
  calc
    _ ≤ ‖lossDefect M‖^2 * ‖r‖^2 := ha
    _ ≤ ‖lossDefect M‖^2 * (C * ‖z‖^2) := mul_le_mul_of_nonneg_left hs (sq_nonneg _)
    _ = _ := by rw [lossDefect_norm_sq M hM hc, hz]; ring

include hM hc hU0 hU1 hω hωm hrowInt hrow in
/-- The adjoint-product quadratic form of the same concrete bound. -/
theorem continuousOneLossNoise_relative_form (x : Space n) :
    (inner ℂ x (((continuousOneLossNoise M μ (fun a => U a (PiLp.single 2 0 1))
      (fun a => U a (PiLp.single 2 1 1))).adjoint.comp
      (continuousOneLossNoise M μ (fun a => U a (PiLp.single 2 0 1))
      (fun a => U a (PiLp.single 2 1 1)))) x)).re ≤
      C * ‖1 - M^2‖ * (inner ℂ x (continuousFrameHamiltonian μ
        (fun a => exteriorSquare M.toLinearMap
          (wedgePair (U a (PiLp.single 2 0 1)) (U a (PiLp.single 2 1 1)))) x)).re := by
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
  simpa only [norm_sq_eq_re_inner (𝕜 := ℂ), RCLike.re_eq_complex_re] using
    continuousOneLossNoise_relative M μ hM hc U hU0 hU1 ω hω hωm C hrowInt hrow x

end VortexGap.Fermion

