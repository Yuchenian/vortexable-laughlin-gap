import VortexGap.Frame.ContinuousSchurRows

noncomputable section
set_option autoImplicit false
namespace VortexGap.Frame
open MeasureTheory
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α]
  (μ : Measure α) [SFinite μ] (k : α → α → ℝ) (ω u : α → ℝ)

theorem schurKernel_norm_le
    (hk : ∀ x y, 0 ≤ k x y) (hs : ∀ x y, k x y = k y x) (hω : ∀ x, 0 < ω x)
    (z : α × α) :
    ‖k z.1 z.2 * u z.1 * u z.2‖ ≤
      (schurRowDensity k ω u z + schurRowDensity k ω u z.swap) / 2 := by
  have h := weighted_schur_pair 1 1 (ω z.1) (ω z.2) |u z.1| |u z.2|
    (by norm_num) (by norm_num) (hω _) (hω _)
  norm_num only [Real.sqrt_one, one_mul, mul_one, sq_abs] at h
  have hm := mul_le_mul_of_nonneg_left h (hk z.1 z.2)
  have he : k z.1 z.2 * ((ω z.2 / ω z.1) * (u z.1)^2 +
      (ω z.1 / ω z.2) * (u z.2)^2) =
      schurRowDensity k ω u z + schurRowDensity k ω u z.swap := by
    simp only [schurRowDensity, Prod.fst_swap, Prod.snd_swap, hs z.2 z.1]
    ring
  rw [he] at hm
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hk z.1 z.2)]
  nlinarith only [hm]

/-- The kernel quadratic form is integrable; this is not an extra Schur premise. -/
theorem schurKernel_integrable
    (hk : ∀ x y, 0 ≤ k x y) (hs : ∀ x y, k x y = k y x)
    (hkm : AEStronglyMeasurable (Function.uncurry k) (μ.prod μ))
    (hω : ∀ x, 0 < ω x) (hωm : AEStronglyMeasurable ω μ) (hu : MemLp u 2 μ)
    (C : ℝ) (hrowInt : ∀ᵐ x ∂μ, Integrable (fun y => k x y * ω y) μ)
    (hrow : ∀ᵐ x ∂μ, (∫ y, k x y * ω y ∂μ) ≤ C * ω x) :
    Integrable (fun z : α × α => k z.1 z.2 * u z.1 * u z.2) (μ.prod μ) := by
  have hi := schurRowDensity_integrable μ k ω u hk hkm hω hωm hu C hrowInt hrow
  apply ((hi.add hi.swap).div_const 2).mono'
    ((hkm.mul hu.aestronglyMeasurable.comp_fst).mul hu.aestronglyMeasurable.comp_snd)
  exact Filter.Eventually.of_forall (schurKernel_norm_le k ω u hk hs hω)

/-- Weighted integral Schur with explicit integrable rows and proved Fubini prerequisites. -/
theorem integral_weighted_schur_quadratic
    (hk : ∀ x y, 0 ≤ k x y) (hs : ∀ x y, k x y = k y x)
    (hkm : AEStronglyMeasurable (Function.uncurry k) (μ.prod μ))
    (hω : ∀ x, 0 < ω x) (hωm : AEStronglyMeasurable ω μ) (hu : MemLp u 2 μ)
    (C : ℝ) (hrowInt : ∀ᵐ x ∂μ, Integrable (fun y => k x y * ω y) μ)
    (hrow : ∀ᵐ x ∂μ, (∫ y, k x y * ω y ∂μ) ≤ C * ω x) :
    (∫ z : α × α, k z.1 z.2 * u z.1 * u z.2 ∂μ.prod μ) ≤ C * ∫ x, (u x)^2 ∂μ := by
  have hi := schurRowDensity_integrable μ k ω u hk hkm hω hωm hu C hrowInt hrow
  have hf := schurKernel_integrable μ k ω u hk hs hkm hω hωm hu C hrowInt hrow
  have hb : (∫ z : α × α, k z.1 z.2 * u z.1 * u z.2 ∂μ.prod μ) ≤
      ∫ z, (schurRowDensity k ω u z + schurRowDensity k ω u z.swap) / 2 ∂μ.prod μ := by
    apply integral_mono_ae hf ((hi.add hi.swap).div_const 2)
    apply Filter.Eventually.of_forall
    intro z
    change k z.1 z.2 * u z.1 * u z.2 ≤
      (schurRowDensity k ω u z + schurRowDensity k ω u z.swap) / 2
    exact (le_abs_self _).trans
      (by simpa only [Real.norm_eq_abs] using schurKernel_norm_le k ω u hk hs hω z)
  have he : (∫ z, (schurRowDensity k ω u z + schurRowDensity k ω u z.swap) / 2 ∂μ.prod μ) =
      ∫ z, schurRowDensity k ω u z ∂μ.prod μ := by
    simp_rw [div_eq_mul_inv]
    have his : Integrable (fun z : α × α => schurRowDensity k ω u z.swap) (μ.prod μ) := hi.swap
    rw [integral_mul_const, integral_add hi his, integral_prod_swap]
    ring
  rw [he] at hb
  exact hb.trans (schurRowDensity_integral_le μ k ω u hk hkm hω hωm hu C hrowInt hrow)

end VortexGap.Frame

