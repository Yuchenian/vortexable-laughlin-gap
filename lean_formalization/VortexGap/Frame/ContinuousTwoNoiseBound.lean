import VortexGap.Frame.ContinuousTwoNoise

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory
open scoped InnerProduct ENNReal ComplexOrder

variable {n : ℕ}
  (M : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
  {α : Type*} [MeasurableSpace α]
  (μ : Measure α) (p : α → PairSpace n) (hp : MemLp p 2 μ)
  (β : ℝ) (hβ : 0 ≤ β)
  (hQ : ∀ q : PairSpace n, (inner ℂ q (continuousPairOperator μ p q)).re ≤ β * ‖q‖^2)

include hp hβ hQ in
/-- Dimension-independent estimate before bounding the exterior square of the loss defect. -/
theorem continuousTwoLossNoise_exterior_bound (x : Space n) :
    ‖continuousTwoLossNoise M μ p x‖^2 ≤
      β * ‖(exteriorSquare (lossDefect M).toLinearMap).toContinuousLinearMap‖^2 *
        (inner ℂ x (continuousFrameHamiltonian μ
          (fun a => exteriorSquare M.toLinearMap (p a)) x)).re := by
  rw [continuousTwoLossNoise_factorization M μ p hp x, pairEnvironmentEmbed_norm_sq]
  let z := continuousFrameAnalysis μ (fun a => exteriorSquare M.toLinearMap (p a))
    (filteredPair_memLp M μ p hp) x
  have ha := pairAmplify_norm_le (exteriorSquare (lossDefect M).toLinearMap)
    (continuousPairSynthesisStack μ p hp z)
  have ha2 := (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr ha
  rw [mul_pow] at ha2
  have hs := mul_le_mul_of_nonneg_left
    (continuousPairSynthesisStack_norm_sq_le μ p hp β hβ hQ z)
    (sq_nonneg ‖(exteriorSquare (lossDefect M).toLinearMap).toContinuousLinearMap‖)
  have hz := continuousFrameAnalysis_energy μ _ (filteredPair_memLp M μ p hp) x
  change ‖z‖^2 = _ at hz
  calc
    _ ≤ ‖(exteriorSquare (lossDefect M).toLinearMap).toContinuousLinearMap‖^2 * (β * ‖z‖^2) := ha2.trans hs
    _ = _ := by rw [hz]; ring

include hp hβ hQ in
/-- Actual continuous-label CAR X2 bound, derived from the raw pair operator Q. -/
theorem continuousTwoLossNoise_relative (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1) (x : Space n) :
    ‖continuousTwoLossNoise M μ p x‖^2 ≤ β * ‖1 - M^2‖^2 *
      (inner ℂ x (continuousFrameHamiltonian μ (fun a => exteriorSquare M.toLinearMap (p a)) x)).re := by
  have he := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
    (lossDefect_exteriorSquare_norm_le M hM hc)
  have hx : 0 ≤ (inner ℂ x
      (continuousFrameHamiltonian μ (fun a => exteriorSquare M.toLinearMap (p a)) x)).re := by
    rw [← continuousFrameAnalysis_energy μ _ (filteredPair_memLp M μ p hp)]
    exact sq_nonneg _
  exact (continuousTwoLossNoise_exterior_bound M μ p hp β hβ hQ x).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he hβ) hx)

include hp hβ hQ in
theorem continuousTwoLossNoise_relative_form (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1) (x : Space n) :
    (inner ℂ x (((continuousTwoLossNoise M μ p).adjoint.comp
      (continuousTwoLossNoise M μ p)) x)).re ≤ β * ‖1 - M^2‖^2 *
      (inner ℂ x (continuousFrameHamiltonian μ (fun a => exteriorSquare M.toLinearMap (p a)) x)).re := by
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
  simpa only [norm_sq_eq_re_inner (𝕜 := ℂ), RCLike.re_eq_complex_re] using
    continuousTwoLossNoise_relative M μ p hp β hβ hQ hM hc x

end VortexGap.Fermion

