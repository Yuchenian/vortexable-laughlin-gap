import VortexGap.Frame.ContinuousPairLift

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory
open scoped InnerProduct ENNReal

variable {α : Type*} [MeasurableSpace α] {n : ℕ}
  (μ : Measure α) (p : α → PairSpace n) (hp : MemLp p 2 μ)

include hp in
theorem pairInner_memLp : MemLp (fun a => innerSL ℂ (p a)) 2 μ := by
  apply hp.of_le_mul (c := 1) ((innerSL ℂ).continuous.comp_aestronglyMeasurable hp.aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun a => by
    simp only [innerSL_apply_norm, one_mul, le_refl]

/-- Actual coefficient analysis, with inner product antilinear in the pair. -/
def continuousPairAnalysis : PairSpace n →L[ℂ] Lp ℂ 2 μ :=
  Frame.operatorAnalysis μ (fun a => innerSL ℂ (p a)) (pairInner_memLp μ p hp)

/-- Actual continuous synthesis; its integral formula is proved below. -/
def continuousPairSynthesis : Lp ℂ 2 μ →L[ℂ] PairSpace n :=
  (continuousPairAnalysis μ p hp).adjoint

theorem continuousPairAnalysis_ae (q : PairSpace n) :
    continuousPairAnalysis μ p hp q =ᵐ[μ] fun a => inner ℂ (p a) q :=
  Frame.operatorAnalysis_ae μ _ _ q

include hp in
theorem continuousPairSynthesis_integrable (f : Lp ℂ 2 μ) :
    Integrable (fun a => (f a) • p a) μ := by
  simpa only [ContinuousLinearMap.adjoint_innerSL_apply, ContinuousLinearMap.toSpanSingleton_apply]
    using Frame.operatorSynthesis_integrable μ (fun a => innerSL ℂ (p a)) (pairInner_memLp μ p hp) f

theorem continuousPairSynthesis_apply (f : Lp ℂ 2 μ) :
    continuousPairSynthesis μ p hp f = ∫ a, (f a) • p a ∂μ := by
  rw [continuousPairSynthesis, continuousPairAnalysis, Frame.operatorAnalysis_adjoint_apply]
  simp only [ContinuousLinearMap.adjoint_innerSL_apply, ContinuousLinearMap.toSpanSingleton_apply]

theorem continuousPairSynthesis_adjoint :
    (continuousPairSynthesis μ p hp).adjoint = continuousPairAnalysis μ p hp := by
  exact ContinuousLinearMap.adjoint_adjoint _

/-- The raw pair-frame operator is proved to be S S*, rather than assumed so. -/
theorem continuousPairSynthesis_gram :
    (continuousPairSynthesis μ p hp).comp (continuousPairSynthesis μ p hp).adjoint =
      continuousPairOperator μ p := by
  rw [continuousPairSynthesis_adjoint]
  change (continuousPairAnalysis μ p hp).adjoint.comp (continuousPairAnalysis μ p hp) = _
  rw [continuousPairAnalysis, Frame.operatorAnalysis_gram]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun a => by
    change (innerSL ℂ (p a)).adjoint.comp (innerSL ℂ (p a)) = InnerProductSpace.rankOne ℂ (p a) (p a)
    rw [ContinuousLinearMap.adjoint_innerSL_apply]
    rfl

theorem continuousPairAnalysis_energy (q : PairSpace n) :
    ‖continuousPairAnalysis μ p hp q‖^2 = (inner ℂ q (continuousPairOperator μ p q)).re := by
  rw [← continuousPairSynthesis_gram μ p hp, ContinuousLinearMap.comp_apply,
    continuousPairSynthesis, ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearMap.adjoint_adjoint, ← RCLike.re_eq_complex_re,
    ← norm_sq_eq_re_inner (𝕜 := ℂ)]

/-- Uniform synthesis control from the raw two-particle quadratic bound. -/
theorem continuousPairSynthesis_norm_sq_le (β : ℝ) (hβ : 0 ≤ β)
    (hQ : ∀ q : PairSpace n, (inner ℂ q (continuousPairOperator μ p q)).re ≤ β * ‖q‖^2)
    (f : Lp ℂ 2 μ) : ‖continuousPairSynthesis μ p hp f‖^2 ≤ β * ‖f‖^2 := by
  let S := continuousPairSynthesis μ p hp
  have ha : ‖S.adjoint (S f)‖^2 ≤ β * ‖S f‖^2 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), ContinuousLinearMap.adjoint_inner_left,
      RCLike.re_eq_complex_re]
    change (inner ℂ (S f) ((S.comp S.adjoint) (S f))).re ≤ _
    rw [continuousPairSynthesis_gram μ p hp]
    exact hQ _
  have hc : ‖S f‖^2 ≤ ‖S.adjoint (S f)‖ * ‖f‖ := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), ← ContinuousLinearMap.adjoint_inner_left S f (S f)]
    exact re_inner_le_norm (𝕜 := ℂ) _ _
  have hc2 := (sq_le_sq₀ (sq_nonneg ‖S f‖)
    (mul_nonneg (norm_nonneg (S.adjoint (S f))) (norm_nonneg f))).mpr hc
  rw [mul_pow] at hc2
  have hh := mul_le_mul_of_nonneg_right ha (sq_nonneg ‖f‖)
  change ‖S f‖^2 ≤ β * ‖f‖^2
  by_cases hz : ‖S f‖ = 0
  · rw [hz, zero_pow (by decide)]
    exact mul_nonneg hβ (sq_nonneg _)
  · have hpos : 0 < ‖S f‖^2 := sq_pos_of_ne_zero hz
    nlinarith only [hc2, hh, hpos]

include hp in
theorem continuousPairOperator_positive : (continuousPairOperator μ p).IsPositive := by
  rw [← continuousPairSynthesis_gram μ p hp, continuousPairSynthesis]
  simpa only [ContinuousLinearMap.adjoint_adjoint] using
    ContinuousLinearMap.isPositive_adjoint_comp_self (continuousPairAnalysis μ p hp)

theorem continuousPairSynthesis_congr_ae (q : α → PairSpace n) (hq : MemLp q 2 μ)
    (heq : p =ᵐ[μ] q) : continuousPairSynthesis μ p hp = continuousPairSynthesis μ q hq := by
  apply congrArg ContinuousLinearMap.adjoint
  apply Frame.operatorAnalysis_congr_ae
  filter_upwards [heq] with a ha
  rw [ha]

end VortexGap.Fermion
