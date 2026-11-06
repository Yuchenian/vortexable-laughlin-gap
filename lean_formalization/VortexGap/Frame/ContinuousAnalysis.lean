import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic

noncomputable section
set_option autoImplicit false
namespace VortexGap.Frame
open MeasureTheory
open scoped InnerProduct ENNReal

variable {α E F : Type*} [MeasurableSpace α]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  (μ : Measure α) (T : α → E →L[ℂ] F) (hT : MemLp T 2 μ)

include hT in
/-- Operator-norm square integrability controls application to every vector.
Bounded measurable families on finite measure spaces satisfy this hypothesis. -/
theorem operatorApply_memLp (x : E) : MemLp (fun a => T a x) 2 μ := by
  apply hT.of_le_mul (hT.aestronglyMeasurable.apply_continuousLinearMap x)
  exact Filter.Eventually.of_forall fun a => by simpa only [mul_comm] using (T a).le_opNorm x

def operatorAnalysisLinear : E →ₗ[ℂ] Lp F 2 μ where
  toFun x := (operatorApply_memLp μ T hT x).toLp (fun a => T a x)
  map_add' x y := by
    rw [← MemLp.toLp_add]
    apply MemLp.toLp_congr
    exact Filter.Eventually.of_forall fun a => (T a).map_add x y
  map_smul' z x := by
    rw [← MemLp.toLp_const_smul]
    apply MemLp.toLp_congr
    exact Filter.Eventually.of_forall fun a => (T a).map_smul z x

theorem operatorAnalysisLinear_ae (x : E) :
    operatorAnalysisLinear μ T hT x =ᵐ[μ] fun a => T a x :=
  (operatorApply_memLp μ T hT x).coeFn_toLp

theorem operatorAnalysisLinear_norm_le (x : E) :
    ‖operatorAnalysisLinear μ T hT x‖ ≤ ‖hT.toLp T‖ * ‖x‖ := by
  rw [mul_comm]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [operatorAnalysisLinear_ae μ T hT x, hT.coeFn_toLp] with a ha hb
  rw [ha, hb, mul_comm]
  exact (T a).le_opNorm x

/-- Actual analysis into the quotient L2 space; its representative is specified a.e. -/
def operatorAnalysis : E →L[ℂ] Lp F 2 μ :=
  (operatorAnalysisLinear μ T hT).mkContinuous ‖hT.toLp T‖ (operatorAnalysisLinear_norm_le μ T hT)

theorem operatorAnalysis_ae (x : E) :
    operatorAnalysis μ T hT x =ᵐ[μ] fun a => T a x := operatorAnalysisLinear_ae μ T hT x

theorem operatorAnalysis_norm_le (x : E) :
    ‖operatorAnalysis μ T hT x‖ ≤ ‖hT.toLp T‖ * ‖x‖ := operatorAnalysisLinear_norm_le μ T hT x

theorem operatorAnalysis_congr_ae (S : α → E →L[ℂ] F) (hS : MemLp S 2 μ)
    (hTS : T =ᵐ[μ] S) : operatorAnalysis μ T hT = operatorAnalysis μ S hS := by
  apply ContinuousLinearMap.ext
  intro x
  apply Lp.ext
  filter_upwards [operatorAnalysis_ae μ T hT x, operatorAnalysis_ae μ S hS x, hTS]
    with a ha hb hc
  rw [ha, hb, hc]

theorem operatorAnalysis_inner_integral (x y : E) :
    inner ℂ (operatorAnalysis μ T hT x) (operatorAnalysis μ T hT y) =
      ∫ a, inner ℂ (T a x) (T a y) ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [operatorAnalysis_ae μ T hT x, operatorAnalysis_ae μ T hT y] with a ha hb
  rw [ha, hb]

include hT in
theorem operatorApply_inner_integrable (x y : E) :
    Integrable (fun a => inner ℂ (T a x) (T a y)) μ := by
  apply (integrable_congr (show (fun a => inner ℂ (operatorAnalysis μ T hT x a)
      (operatorAnalysis μ T hT y a)) =ᵐ[μ] (fun a => inner ℂ (T a x) (T a y)) from ?_)).mp
    (L2.integrable_inner (operatorAnalysis μ T hT x) (operatorAnalysis μ T hT y))
  filter_upwards [operatorAnalysis_ae μ T hT x, operatorAnalysis_ae μ T hT y] with a ha hb
  rw [ha, hb]

theorem operatorAnalysis_norm_sq (x : E) :
    ‖operatorAnalysis μ T hT x‖^2 = ∫ a, ‖T a x‖^2 ∂μ := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), operatorAnalysis_inner_integral,
    ← integral_re (operatorApply_inner_integrable μ T hT x x)]
  congr 1
  funext a
  exact (norm_sq_eq_re_inner (𝕜 := ℂ) (T a x)).symm

end VortexGap.Frame
