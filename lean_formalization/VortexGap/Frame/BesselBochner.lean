import VortexGap.Frame.BesselGramCutoff
import VortexGap.Frame.ContinuousSynthesis
noncomputable section
set_option autoImplicit false
namespace VortexGap.Frame
open MeasureTheory
open scoped InnerProduct ENNReal
variable {α E F : Type*} [MeasurableSpace α]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  (μ : Measure α) (T : α → E →L[ℂ] F)
  (hT : ∀ x, MemLp (fun a => T a x) 2 μ)
  (β : ℝ) (hβ : 0 ≤ β) (hb : ∀ x : E, (∫ a, ‖T a x‖^2 ∂μ) ≤ β * ‖x‖^2)

/-- On an integrable field, the weak/Bessel construction agrees with the prior Bochner construction. -/
theorem besselAnalysis_eq_operatorAnalysis (hEnv : MemLp T 2 μ) :
    besselAnalysis μ T hT β hβ hb = operatorAnalysis μ T hEnv := by
  apply ContinuousLinearMap.ext
  intro x
  apply Lp.ext
  filter_upwards [besselAnalysis_ae μ T hT β hβ hb x, operatorAnalysis_ae μ T hEnv x]
    with a ha hb'
  rw [ha,hb']

theorem besselGram_integral (hEnv : MemLp T 2 μ) :
    (besselAnalysis μ T hT β hβ hb).adjoint.comp (besselAnalysis μ T hT β hβ hb) =
      ∫ a, (T a).adjoint.comp (T a) ∂μ := by
  rw [besselAnalysis_eq_operatorAnalysis μ T hT β hβ hb hEnv]
  exact operatorAnalysis_gram μ T hEnv

/-- Only local integrability is used to identify a cutoff with a Bochner integral.
The full frame may fail the global operator-norm L2 condition. -/
theorem besselGramCutoff_integral (s : Set α) (hs : MeasurableSet s)
    (hEnv : MemLp T 2 (μ.restrict s)) :
    l2GramCutoff μ (besselAnalysis μ T hT β hβ hb) s hs =
      ∫ a in s, (T a).adjoint.comp (T a) ∂μ := by
  apply ContinuousLinearMap.ext
  intro y
  apply ext_inner_left ℂ
  intro x
  rw [besselGramCutoff_inner,
    ← operatorAnalysis_gram (μ.restrict s) T hEnv,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    operatorAnalysis_inner_integral]
end VortexGap.Frame
