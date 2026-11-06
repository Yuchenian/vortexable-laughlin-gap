import VortexGap.Frame.OneNoiseFactorization

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open VortexGap.Frame
open scoped BigOperators InnerProduct ComplexOrder

/-- The one-environment estimate derived from concrete CAR columns and raw frame overlap. -/
theorem oneLossNoise_relative {n : ℕ} {ι : Type*} [Fintype ι]
    (M : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (U : ι → TwoFrame n)
    (ω : ι → ℝ) (hω : ∀ i, 0 < ω i) (C : ℝ)
    (hrow : ∀ i, ∑ j, w j * traceNormTwo (twoFrameOverlap (U i) (U j)) * ω j ≤ C * ω i)
    (x : Space n) :
    ‖oneLossNoise M w (fun i => U i (PiLp.single 2 0 1))
      (fun i => U i (PiLp.single 2 1 1)) x‖^2 ≤
      C * ‖1 - M^2‖ * (inner ℂ x (filteredHamiltonian M w
        (fun i => wedgePair (U i (PiLp.single 2 0 1)) (U i (PiLp.single 2 1 1))) x)).re := by
  let u := fun i => U i (PiLp.single 2 0 1)
  let v := fun i => U i (PiLp.single 2 1 1)
  let p := fun i => wedgePair (u i) (v i)
  let z := frameAnalysis w (fun i => exteriorSquare M.toLinearMap (p i)) x
  let r := oneFrameSynthesis M w u v z
  rw [oneLossNoise_factorization M w hw, orbitalEnvironmentEmbed_norm_sq]
  change ‖orbitalAmplify (lossDefect M) r‖^2 ≤ _
  have ha := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
    (orbitalAmplify_norm_le (lossDefect M) r)
  rw [mul_pow] at ha
  have hs : ‖r‖^2 ≤ C * ‖z‖^2 := oneFrameSynthesis_norm_sq_le M hc w hw U ω hω C hrow z
  have hz : ‖z‖^2 = (inner ℂ x (filteredHamiltonian M w p x)).re :=
    filtered_frameAnalysis_norm_sq M w hw p x
  calc
    _ ≤ ‖lossDefect M‖^2 * ‖r‖^2 := ha
    _ ≤ ‖lossDefect M‖^2 * (C * ‖z‖^2) := mul_le_mul_of_nonneg_left hs (sq_nonneg _)
    _ = _ := by rw [lossDefect_norm_sq M hM hc, hz]; ring

/-- Real quadratic form of the same concrete estimate. -/
theorem oneLossNoise_relative_form {n : ℕ} {ι : Type*} [Fintype ι]
    (M : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (U : ι → TwoFrame n)
    (ω : ι → ℝ) (hω : ∀ i, 0 < ω i) (C : ℝ)
    (hrow : ∀ i, ∑ j, w j * traceNormTwo (twoFrameOverlap (U i) (U j)) * ω j ≤ C * ω i)
    (x : Space n) :
    (inner ℂ x (((oneLossNoise M w (fun i => U i (PiLp.single 2 0 1))
      (fun i => U i (PiLp.single 2 1 1))).adjoint.comp
      (oneLossNoise M w (fun i => U i (PiLp.single 2 0 1))
      (fun i => U i (PiLp.single 2 1 1)))) x)).re ≤
      C * ‖1 - M^2‖ * (inner ℂ x (filteredHamiltonian M w
        (fun i => wedgePair (U i (PiLp.single 2 0 1)) (U i (PiLp.single 2 1 1))) x)).re := by
  rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right]
  simpa only [norm_sq_eq_re_inner (𝕜 := ℂ), RCLike.re_eq_complex_re] using
    oneLossNoise_relative M hM hc w hw U ω hω C hrow x

end VortexGap.Fermion
