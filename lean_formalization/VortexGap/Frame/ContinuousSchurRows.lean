import VortexGap.Frame.WeightedSchur
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.L2Space

noncomputable section
set_option autoImplicit false
namespace VortexGap.Frame
open MeasureTheory
open scoped ENNReal

/-- Nonnegative weighted Young majorant on the product label space. -/
def schurRowDensity {α : Type*} (k : α → α → ℝ) (ω u : α → ℝ) (z : α × α) : ℝ :=
  (u z.1)^2 / ω z.1 * (k z.1 z.2 * ω z.2)

variable {α : Type*} [MeasurableSpace α]
  (μ : Measure α) [SFinite μ]
  (k : α → α → ℝ) (ω u : α → ℝ)

theorem schurRowDensity_nonneg (hk : ∀ x y, 0 ≤ k x y) (hω : ∀ x, 0 < ω x) (z : α × α) :
    0 ≤ schurRowDensity k ω u z :=
  mul_nonneg (div_nonneg (sq_nonneg _) (hω z.1).le) (mul_nonneg (hk _ _) (hω z.2).le)

theorem schurRowDensity_measurable
    (hk : AEStronglyMeasurable (Function.uncurry k) (μ.prod μ))
    (hω : AEStronglyMeasurable ω μ) (hu : AEStronglyMeasurable u μ) :
    AEStronglyMeasurable (schurRowDensity k ω u) (μ.prod μ) := by
  have hd : AEStronglyMeasurable (fun z : α × α => (u z.1)^2 / ω z.1) (μ.prod μ) :=
    ((hu.comp_fst.pow 2).aemeasurable.div hω.comp_fst.aemeasurable).aestronglyMeasurable
  exact hd.mul (hk.mul hω.comp_snd)

theorem schurRowDensity_row_integrable
    (hrow : ∀ᵐ x ∂μ, Integrable (fun y => k x y * ω y) μ) :
    ∀ᵐ x ∂μ, Integrable (fun y => schurRowDensity k ω u (x,y)) μ := by
  filter_upwards [hrow] with x hx
  exact hx.const_mul ((u x)^2 / ω x)

theorem schurRowDensity_row_bound
    (hk : ∀ x y, 0 ≤ k x y) (hω : ∀ x, 0 < ω x) (C : ℝ)
    (hrow : ∀ᵐ x ∂μ, (∫ y, k x y * ω y ∂μ) ≤ C * ω x) :
    ∀ᵐ x ∂μ, (∫ y, ‖schurRowDensity k ω u (x,y)‖ ∂μ) ≤ C * (u x)^2 := by
  filter_upwards [hrow] with x hx
  simp_rw [Real.norm_eq_abs, abs_of_nonneg (schurRowDensity_nonneg k ω u hk hω _)]
  change (∫ y, ((u x)^2 / ω x) * (k x y * ω y) ∂μ) ≤ _
  rw [integral_const_mul]
  calc
    _ ≤ ((u x)^2 / ω x) * (C * ω x) :=
      mul_le_mul_of_nonneg_left hx (div_nonneg (sq_nonneg _) (hω x).le)
    _ = _ := by field_simp [ne_of_gt (hω x)]

/-- Product integrability is derived from integrable weighted rows and their bound. -/
theorem schurRowDensity_integrable
    (hk : ∀ x y, 0 ≤ k x y) (hkm : AEStronglyMeasurable (Function.uncurry k) (μ.prod μ))
    (hω : ∀ x, 0 < ω x) (hωm : AEStronglyMeasurable ω μ) (hu : MemLp u 2 μ)
    (C : ℝ) (hrowInt : ∀ᵐ x ∂μ, Integrable (fun y => k x y * ω y) μ)
    (hrow : ∀ᵐ x ∂μ, (∫ y, k x y * ω y ∂μ) ≤ C * ω x) :
    Integrable (schurRowDensity k ω u) (μ.prod μ) := by
  have hm := schurRowDensity_measurable μ k ω u hkm hωm hu.aestronglyMeasurable
  apply (integrable_prod_iff hm).mpr
  refine ⟨schurRowDensity_row_integrable μ k ω u hrowInt, ?_⟩
  have hu2 : Integrable (fun x => (u x)^2) μ := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).mp hu
  apply (hu2.const_mul C).mono' hm.norm.integral_prod_right'
  filter_upwards [schurRowDensity_row_bound μ k ω u hk hω C hrow] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun y => norm_nonneg _))]
  exact hx

/-- The row majorant has the expected C times L2-energy bound after justified Fubini. -/
theorem schurRowDensity_integral_le
    (hk : ∀ x y, 0 ≤ k x y) (hkm : AEStronglyMeasurable (Function.uncurry k) (μ.prod μ))
    (hω : ∀ x, 0 < ω x) (hωm : AEStronglyMeasurable ω μ) (hu : MemLp u 2 μ)
    (C : ℝ) (hrowInt : ∀ᵐ x ∂μ, Integrable (fun y => k x y * ω y) μ)
    (hrow : ∀ᵐ x ∂μ, (∫ y, k x y * ω y ∂μ) ≤ C * ω x) :
    (∫ z, schurRowDensity k ω u z ∂μ.prod μ) ≤ C * ∫ x, (u x)^2 ∂μ := by
  have hi := schurRowDensity_integrable μ k ω u hk hkm hω hωm hu C hrowInt hrow
  rw [integral_prod _ hi, ← integral_const_mul]
  have hu2 : Integrable (fun x => (u x)^2) μ := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).mp hu
  apply integral_mono_ae hi.integral_prod_left (hu2.const_mul C)
  filter_upwards [schurRowDensity_row_bound μ k ω u hk hω C hrow] with x hx
  simpa only [Real.norm_eq_abs, abs_of_nonneg (schurRowDensity_nonneg k ω u hk hω _)] using hx

end VortexGap.Frame

