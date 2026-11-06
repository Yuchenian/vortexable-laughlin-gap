import VortexGap.Frame.ContinuousSchurOperator
import VortexGap.Frame.L2FiniteFiber
import VortexGap.Frame.LocalBessel

noncomputable section
set_option autoImplicit false
namespace VortexGap.Frame
open MeasureTheory Filter
open scoped InnerProduct ENNReal Topology
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- A synthesis estimate controls its actual Hilbert adjoint with the same constant. -/
theorem analysis_norm_sq_of_adjoint_bound (A : E →L[ℂ] F) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ f, ‖A.adjoint f‖^2 ≤ C * ‖f‖^2) (x : E) :
    ‖A x‖^2 ≤ C * ‖x‖^2 := by
  have hn : ‖A.adjoint‖ ≤ Real.sqrt C := by
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    intro f
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    rw [mul_pow, Real.sq_sqrt hC]
    exact hb f
  rw [ContinuousLinearMap.adjoint.norm_map] at hn
  have hx := A.le_of_opNorm_le hn x
  have hsq := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mpr hx
  simpa only [mul_pow, Real.sq_sqrt hC] using hsq

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [SFinite μ]
  (T : α → E →L[ℂ] F) (hT : MemLp T 2 μ)
  (k : α → α → ℝ) (hk : ∀ a b, 0 ≤ k a b)
  (hs : ∀ a b, k a b = k b a)
  (hkm : AEStronglyMeasurable (Function.uncurry k) (μ.prod μ))
  (ω : α → ℝ) (hω : ∀ a, 0 < ω a) (hωm : AEStronglyMeasurable ω μ)
  (C : ℝ)
  (hrowInt : ∀ᵐ a ∂μ, Integrable (fun b => k a b * ω b) μ)
  (hrow : ∀ᵐ a ∂μ, (∫ b, k a b * ω b ∂μ) ≤ C * ω a)
  (hGram : ∀ a b, ‖(T a).comp (T b).adjoint‖ ≤ k a b)

include hT hk hs hkm hω hωm hrowInt hrow hGram in
/-- Raw weighted Schur rows bound the genuine local Bochner synthesis. -/
theorem operatorAnalysis_adjoint_schur_bound (f : Lp F 2 μ) :
    ‖(operatorAnalysis μ T hT).adjoint f‖^2 ≤ C * ‖f‖^2 := by
  rw [operatorAnalysis_adjoint_apply, l2_norm_sq_integral]
  apply integral_weighted_synthesis_norm_sq μ (fun a => (T a).adjoint)
    f (Lp.memLp f) (operatorSynthesis_integrable μ T hT f)
    k hk hs hkm ω hω hωm C hrowInt hrow
  intro a b
  simpa only [ContinuousLinearMap.adjoint_adjoint] using hGram a b

include hT hk hs hkm hω hωm hrowInt hrow hGram in
/-- The vectorwise L2 bound is derived from Schur, ready for local-to-global extension. -/
theorem operatorAnalysis_schur_bessel (hC : 0 ≤ C) (x : E) :
    (∫ a, ‖T a x‖^2 ∂μ) ≤ C * ‖x‖^2 := by
  rw [← operatorAnalysis_norm_sq μ T hT x]
  exact analysis_norm_sq_of_adjoint_bound (operatorAnalysis μ T hT) C hC
    (operatorAnalysis_adjoint_schur_bound μ T hT k hk hs hkm ω hω hωm C hrowInt hrow hGram) x

end VortexGap.Frame

