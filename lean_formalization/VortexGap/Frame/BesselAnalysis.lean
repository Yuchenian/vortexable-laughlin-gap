import VortexGap.Frame.ContinuousAnalysis
import Mathlib.Analysis.InnerProductSpace.Positive
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

/-- Pointwise L2 analysis. No square-integrable operator-norm envelope is required. -/
def besselAnalysisLinear : E →ₗ[ℂ] Lp F 2 μ where
  toFun x := (hT x).toLp (fun a => T a x)
  map_add' x y := by
    rw [← MemLp.toLp_add]
    apply MemLp.toLp_congr
    exact Filter.Eventually.of_forall fun a => (T a).map_add x y
  map_smul' z x := by
    rw [← MemLp.toLp_const_smul]
    apply MemLp.toLp_congr
    exact Filter.Eventually.of_forall fun a => (T a).map_smul z x

theorem besselAnalysisLinear_ae (x : E) :
    besselAnalysisLinear μ T hT x =ᵐ[μ] fun a => T a x :=
  (hT x).coeFn_toLp

theorem besselAnalysisLinear_inner (x y : E) :
    inner ℂ (besselAnalysisLinear μ T hT x) (besselAnalysisLinear μ T hT y) =
      ∫ a, inner ℂ (T a x) (T a y) ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [besselAnalysisLinear_ae μ T hT x, besselAnalysisLinear_ae μ T hT y]
    with a hx hy
  rw [hx,hy]

include hT in
theorem besselApply_inner_integrable (x y : E) :
    Integrable (fun a => inner ℂ (T a x) (T a y)) μ := by
  apply (integrable_congr (show (fun a => inner ℂ (besselAnalysisLinear μ T hT x a)
      (besselAnalysisLinear μ T hT y a)) =ᵐ[μ] (fun a => inner ℂ (T a x) (T a y)) from ?_)).mp
    (L2.integrable_inner (besselAnalysisLinear μ T hT x) (besselAnalysisLinear μ T hT y))
  filter_upwards [besselAnalysisLinear_ae μ T hT x, besselAnalysisLinear_ae μ T hT y]
    with a hx hy
  rw [hx,hy]

theorem besselAnalysisLinear_norm_sq (x : E) :
    ‖besselAnalysisLinear μ T hT x‖^2 = ∫ a, ‖T a x‖^2 ∂μ := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), besselAnalysisLinear_inner,
    ← integral_re (besselApply_inner_integrable μ T hT x x)]
  congr 1
  funext a
  exact (norm_sq_eq_re_inner (𝕜 := ℂ) (T a x)).symm

variable (β : ℝ) (hβ : 0 ≤ β)
  (hb : ∀ x : E, (∫ a, ‖T a x‖^2 ∂μ) ≤ β * ‖x‖^2)

include hβ hb in
theorem besselAnalysisLinear_norm_le (x : E) :
    ‖besselAnalysisLinear μ T hT x‖ ≤ Real.sqrt β * ‖x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt hβ, besselAnalysisLinear_norm_sq]
  exact hb x

/-- The raw Bessel inequality builds a bounded map on arbitrary measure spaces. -/
def besselAnalysis : E →L[ℂ] Lp F 2 μ :=
  (besselAnalysisLinear μ T hT).mkContinuous (Real.sqrt β)
    (besselAnalysisLinear_norm_le μ T hT β hβ hb)

theorem besselAnalysis_ae (x : E) :
    besselAnalysis μ T hT β hβ hb x =ᵐ[μ] fun a => T a x :=
  besselAnalysisLinear_ae μ T hT x

theorem besselAnalysis_norm_sq (x : E) :
    ‖besselAnalysis μ T hT β hβ hb x‖^2 = ∫ a, ‖T a x‖^2 ∂μ :=
  besselAnalysisLinear_norm_sq μ T hT x

theorem besselAnalysis_opNorm_le :
    ‖besselAnalysis μ T hT β hβ hb‖ ≤ Real.sqrt β :=
  ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    (besselAnalysisLinear_norm_le μ T hT β hβ hb)

theorem besselAnalysis_gram_inner (x y : E) :
    inner ℂ x (((besselAnalysis μ T hT β hβ hb).adjoint.comp
      (besselAnalysis μ T hT β hβ hb)) y) =
      ∫ a, inner ℂ (T a x) (T a y) ∂μ := by
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
  exact besselAnalysisLinear_inner μ T hT x y

theorem besselAnalysis_gram_positive :
    ((besselAnalysis μ T hT β hβ hb).adjoint.comp
      (besselAnalysis μ T hT β hβ hb)).IsPositive :=
  ContinuousLinearMap.isPositive_adjoint_comp_self _

/-- The quotient analysis map is independent of all a.e. choices in the field. -/
theorem besselAnalysis_congr_ae (S : α → E →L[ℂ] F)
    (hS : ∀ x, MemLp (fun a => S a x) 2 μ)
    (hsb : ∀ x : E, (∫ a, ‖S a x‖^2 ∂μ) ≤ β * ‖x‖^2)
    (heq : ∀ x, (fun a => T a x) =ᵐ[μ] fun a => S a x) :
    besselAnalysis μ T hT β hβ hb = besselAnalysis μ S hS β hβ hsb := by
  apply ContinuousLinearMap.ext
  intro x
  apply Lp.ext
  filter_upwards [besselAnalysis_ae μ T hT β hβ hb x,
    besselAnalysis_ae μ S hS β hβ hsb x, heq x] with a ht hs he
  rw [ht,hs,he]
end VortexGap.Frame
