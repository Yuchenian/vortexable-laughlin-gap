import VortexGap.Frame.ContinuousSchur
import VortexGap.Frame.ContinuousSynthesis

noncomputable section
set_option autoImplicit false
namespace VortexGap.Frame
open MeasureTheory
open scoped InnerProduct ENNReal ComplexConjugate

variable {α E F : Type*} [MeasurableSpace α]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  (μ : Measure α) [SFinite μ]

theorem integralGram_integrable (g : α → F) (hg : Integrable g μ) :
    Integrable (fun z : α × α => inner ℂ (g z.1) (g z.2)) (μ.prod μ) := by
  apply (hg.norm.mul_prod hg.norm).mono'
    (hg.aestronglyMeasurable.comp_fst.inner hg.aestronglyMeasurable.comp_snd)
  exact Filter.Eventually.of_forall fun z => norm_inner_le_norm (g z.1) (g z.2)

/-- A genuine product integral identity; absolute integrability was derived above. -/
theorem integralGram_eq (g : α → F) (hg : Integrable g μ) :
    (∫ z : α × α, inner ℂ (g z.1) (g z.2) ∂μ.prod μ) =
      inner ℂ (∫ a, g a ∂μ) (∫ a, g a ∂μ) := by
  rw [integral_prod _ (integralGram_integrable μ g hg)]
  simp_rw [integral_inner hg]
  have he : (fun a => inner ℂ (g a) (∫ b, g b ∂μ)) =
      fun a => conj (inner ℂ (∫ b, g b ∂μ) (g a)) := by
    funext a
    exact (inner_conj_symm _ _).symm
  rw [he, integral_conj, integral_inner hg]
  exact inner_conj_symm _ _

theorem synthesisIntegral_norm_sq (g : α → F) (hg : Integrable g μ) :
    ‖∫ a, g a ∂μ‖^2 =
      ∫ z : α × α, (inner ℂ (g z.1) (g z.2)).re ∂μ.prod μ := by
  change ‖∫ a, g a ∂μ‖^2 =
    ∫ z : α × α, RCLike.re (inner ℂ (g z.1) (g z.2)) ∂μ.prod μ
  rw [integral_re (integralGram_integrable μ g hg), integralGram_eq μ g hg,
    ← norm_sq_eq_re_inner (𝕜 := ℂ)]

theorem synthesisGram_majorant (R S : E →L[ℂ] F) (k : ℝ)
    (hGram : ‖R.adjoint.comp S‖ ≤ k) (x y : E) :
    (inner ℂ (R x) (S y)).re ≤ k * ‖x‖ * ‖y‖ := by
  rw [← ContinuousLinearMap.adjoint_inner_right R]
  calc
    _ ≤ ‖inner ℂ x (R.adjoint (S y))‖ := RCLike.re_le_norm _
    _ ≤ ‖x‖ * ‖R.adjoint (S y)‖ := norm_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖R.adjoint.comp S‖ * ‖y‖) :=
      mul_le_mul_of_nonneg_left ((R.adjoint.comp S).le_opNorm y) (norm_nonneg _)
    _ ≤ ‖x‖ * (k * ‖y‖) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hGram (norm_nonneg _)) (norm_nonneg _)
    _ = _ := by ring

/-- Operator-valued integral Schur. Concrete CAR Gram control is supplied separately. -/
theorem integral_weighted_synthesis_norm_sq (R : α → E →L[ℂ] F)
    (f : α → E) (hf : MemLp f 2 μ) (hRf : Integrable (fun a => R a (f a)) μ)
    (k : α → α → ℝ) (hk : ∀ x y, 0 ≤ k x y) (hs : ∀ x y, k x y = k y x)
    (hkm : AEStronglyMeasurable (Function.uncurry k) (μ.prod μ))
    (ω : α → ℝ) (hω : ∀ x, 0 < ω x) (hωm : AEStronglyMeasurable ω μ)
    (C : ℝ) (hrowInt : ∀ᵐ x ∂μ, Integrable (fun y => k x y * ω y) μ)
    (hrow : ∀ᵐ x ∂μ, (∫ y, k x y * ω y ∂μ) ≤ C * ω x)
    (hGram : ∀ x y, ‖(R x).adjoint.comp (R y)‖ ≤ k x y) :
    ‖∫ a, R a (f a) ∂μ‖^2 ≤ C * ∫ a, ‖f a‖^2 ∂μ := by
  rw [synthesisIntegral_norm_sq μ _ hRf]
  calc
    _ ≤ ∫ z : α × α, k z.1 z.2 * ‖f z.1‖ * ‖f z.2‖ ∂μ.prod μ := by
      apply integral_mono_ae (integralGram_integrable μ _ hRf).re
        (schurKernel_integrable μ k ω (fun a => ‖f a‖) hk hs hkm hω hωm hf.norm C hrowInt hrow)
      exact Filter.Eventually.of_forall fun z =>
        synthesisGram_majorant (R z.1) (R z.2) (k z.1 z.2) (hGram _ _) (f z.1) (f z.2)
    _ ≤ _ := integral_weighted_schur_quadratic μ k ω (fun a => ‖f a‖)
      hk hs hkm hω hωm hf.norm C hrowInt hrow

end VortexGap.Frame

