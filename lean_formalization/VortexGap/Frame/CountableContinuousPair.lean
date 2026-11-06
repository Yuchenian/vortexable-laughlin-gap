import VortexGap.Frame.BesselBochner
import VortexGap.Fermion.CountablePairLimits

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory Filter
open scoped InnerProduct ENNReal Topology ComplexOrder

variable {α : Type*} [MeasurableSpace α]
  (μ : Measure α) (p : α → CountablePairSpace)
  (hp : ∀ q, MemLp (fun a => inner ℂ (p a) q) 2 μ)
  (β : ℝ) (hβ : 0 ≤ β)
  (hb : ∀ q, (∫ a, ‖inner ℂ (p a) q‖^2 ∂μ) ≤ β * ‖q‖^2)

/-- Coefficient analysis of an actual countable-mode pair field.
Only vectorwise L2 integrability is required. -/
def countableContinuousPairAnalysis : CountablePairSpace →L[ℂ] Lp ℂ 2 μ :=
  Frame.besselAnalysis μ (fun a => innerSL ℂ (p a)) hp β hβ hb

/-- The bounded pair operator represented by the frame's weak integral. -/
def countableContinuousPairOperator : CountablePairSpace →L[ℂ] CountablePairSpace :=
  (countableContinuousPairAnalysis μ p hp β hβ hb).adjoint.comp
    (countableContinuousPairAnalysis μ p hp β hβ hb)

/-- Cutoffs act on the actual L2 label analysis, without point-supported label vectors. -/
def countableContinuousPairCutoff (s : Set α) (hs : MeasurableSet s) :
    CountablePairSpace →L[ℂ] CountablePairSpace :=
  Frame.l2GramCutoff μ (countableContinuousPairAnalysis μ p hp β hβ hb) s hs

theorem countableContinuousPairAnalysis_ae (q : CountablePairSpace) :
    countableContinuousPairAnalysis μ p hp β hβ hb q =ᵐ[μ]
      fun a => inner ℂ (p a) q :=
  Frame.besselAnalysis_ae μ _ hp β hβ hb q

theorem countableContinuousPairOperator_inner (q r : CountablePairSpace) :
    inner ℂ q (countableContinuousPairOperator μ p hp β hβ hb r) =
      ∫ a, inner ℂ (inner ℂ (p a) q) (inner ℂ (p a) r) ∂μ :=
  Frame.besselAnalysis_gram_inner μ _ hp β hβ hb q r

theorem countableContinuousPairOperator_positive :
    (countableContinuousPairOperator μ p hp β hβ hb).IsPositive :=
  ContinuousLinearMap.isPositive_adjoint_comp_self _

theorem countableContinuousPairOperator_energy (q : CountablePairSpace) :
    (inner ℂ q (countableContinuousPairOperator μ p hp β hβ hb q)).re =
      ∫ a, ‖inner ℂ (p a) q‖^2 ∂μ := by
  change (inner ℂ q ((countableContinuousPairAnalysis μ p hp β hβ hb).adjoint
    (countableContinuousPairAnalysis μ p hp β hβ hb q))).re = _
  rw [ContinuousLinearMap.adjoint_inner_right, ← RCLike.re_eq_complex_re,
    ← norm_sq_eq_re_inner (𝕜 := ℂ)]
  exact Frame.besselAnalysis_norm_sq μ _ hp β hβ hb q

theorem countableContinuousPairOperator_quadratic_le (q : CountablePairSpace) :
    (inner ℂ q (countableContinuousPairOperator μ p hp β hβ hb q)).re ≤ β * ‖q‖^2 := by
  rw [countableContinuousPairOperator_energy]
  exact hb q

theorem countableContinuousPairCutoff_positive (s : Set α) (hs : MeasurableSet s) :
    (countableContinuousPairCutoff μ p hp β hβ hb s hs).IsPositive :=
  Frame.l2GramCutoff_positive μ _ s hs

theorem countableContinuousPairCutoff_le (s : Set α) (hs : MeasurableSet s) :
    countableContinuousPairCutoff μ p hp β hβ hb s hs ≤
      countableContinuousPairOperator μ p hp β hβ hb :=
  Frame.l2GramCutoff_le μ _ s hs

theorem countableContinuousPairCutoff_norm_le (s : Set α) (hs : MeasurableSet s) :
    ‖countableContinuousPairCutoff μ p hp β hβ hb s hs‖ ≤ β :=
  Frame.besselGramCutoff_norm_le μ _ hp β hβ hb s hs

theorem countableContinuousPairCutoff_tendsto
    (s : ℕ → Set α) (hs : ∀ n, MeasurableSet (s n))
    (hm : Monotone s) (hu : ⋃ n, s n = Set.univ) (q : CountablePairSpace) :
    Tendsto (fun n => countableContinuousPairCutoff μ p hp β hβ hb (s n) (hs n) q)
      atTop (𝓝 (countableContinuousPairOperator μ p hp β hβ hb q)) :=
  Frame.l2GramCutoff_tendsto μ _ s hs hm hu q

/-- Strong cutoff convergence on every complete fixed-N sector. No cutoff gap is used. -/
theorem countableContinuousPairLift_tendsto
    (s : ℕ → Set α) (hs : ∀ n, MeasurableSet (s n))
    (hm : Monotone s) (hu : ⋃ n, s n = Set.univ)
    (N : ℕ) (x : countableSector N) :
    Tendsto (fun n => countablePairLift N
      (countableContinuousPairCutoff μ p hp β hβ hb (s n) (hs n)) x) atTop
      (𝓝 (countablePairLift N (countableContinuousPairOperator μ p hp β hβ hb) x)) :=
  countablePairLift_tendsto N _ _ β hβ
    (fun n => countableContinuousPairCutoff_norm_le μ p hp β hβ hb (s n) (hs n))
    (countableContinuousPairCutoff_tendsto μ p hp β hβ hb s hs hm hu) x

/-- Local norm integrability identifies each cutoff with its genuine rank-one integral. -/
theorem countableContinuousPairCutoff_integral (s : Set α) (hs : MeasurableSet s)
    (hloc : MemLp p 2 (μ.restrict s)) :
    countableContinuousPairCutoff μ p hp β hβ hb s hs =
      ∫ a in s, InnerProductSpace.rankOne ℂ (p a) (p a) ∂μ := by
  have hfield : MemLp (fun a => innerSL ℂ (p a)) 2 (μ.restrict s) := by
    apply hloc.of_le_mul (c := 1)
      ((innerSL ℂ).continuous.comp_aestronglyMeasurable hloc.aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun a => by
      simp only [innerSL_apply_norm, one_mul, le_refl]
  change Frame.l2GramCutoff μ
    (Frame.besselAnalysis μ (fun a => innerSL ℂ (p a)) hp β hβ hb) s hs = _
  rw [Frame.besselGramCutoff_integral μ _ hp β hβ hb s hs hfield]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun a => by
    change (innerSL ℂ (p a)).adjoint.comp (innerSL ℂ (p a)) =
      InnerProductSpace.rankOne ℂ (p a) (p a)
    rw [ContinuousLinearMap.adjoint_innerSL_apply]
    rfl

end VortexGap.Fermion

