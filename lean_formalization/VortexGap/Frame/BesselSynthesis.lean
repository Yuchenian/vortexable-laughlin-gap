import VortexGap.Frame.BesselBochner

noncomputable section
set_option autoImplicit false
namespace VortexGap.Frame
open MeasureTheory Filter
open scoped InnerProduct ENNReal Topology
variable {α E F : Type*} [MeasurableSpace α]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  (μ : Measure α) (T : α → E →L[ℂ] F)

theorem besselSynthesis_local_integrable (s : Set α)
    (hEnv : MemLp T 2 (μ.restrict s)) (f : Lp F 2 μ) :
    Integrable (fun a => (T a).adjoint (f a)) (μ.restrict s) := by
  have hf : MemLp (fun a => f a) 2 (μ.restrict s) :=
    (Lp.memLp f).mono_measure Measure.restrict_le_self
  have hm := (ContinuousLinearMap.adjoint : (E →L[ℂ] F) ≃ₗᵢ⋆[ℂ] (F →L[ℂ] E)).continuous.comp_aestronglyMeasurable hEnv.aestronglyMeasurable
  apply (hEnv.norm.integrable_mul hf.norm).mono'
    ((ContinuousLinearMap.id ℂ (F →L[ℂ] E)).aestronglyMeasurable_comp₂ hm hf.aestronglyMeasurable)
  exact Eventually.of_forall fun a => by
    simpa only [ContinuousLinearMap.id_apply, ContinuousLinearMap.compL_apply,
      Pi.mul_apply, ContinuousLinearMap.adjoint.norm_map] using (T a).adjoint.le_opNorm (f a)

variable (hT : ∀ x, MemLp (fun a => T a x) 2 μ)
  (β : ℝ) (hβ : 0 ≤ β) (hb : ∀ x : E, (∫ a, ‖T a x‖^2 ∂μ) ≤ β * ‖x‖^2)

/-- Local Bochner synthesis agrees with the cutoff of the actual global adjoint.
No absolute integral over all labels is asserted. -/
theorem besselSynthesis_cutoff_integral (s : Set α) (hs : MeasurableSet s)
    (hEnv : MemLp T 2 (μ.restrict s)) (f : Lp F 2 μ) :
    (besselAnalysis μ T hT β hβ hb).adjoint (l2Cutoff μ s hs f) =
      ∫ a in s, (T a).adjoint (f a) ∂μ := by
  apply ext_inner_left ℂ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_right, L2.inner_def,
    ← integral_inner (besselSynthesis_local_integrable μ T s hEnv f),
    ← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [besselAnalysis_ae μ T hT β hβ hb x,
    l2Cutoff_ae μ s hs f] with a hx hf
  rw [hx,hf]
  by_cases ha : a ∈ s
  · simp only [Set.indicator_of_mem ha]
    exact (T a).adjoint_inner_right x (f a) |>.symm
  · simp [ha]

/-- Restricted genuine synthesis integrals converge to the bounded global synthesis. -/
theorem besselSynthesis_integral_tendsto (s : ℕ → Set α)
    (hs : ∀ n, MeasurableSet (s n)) (hm : Monotone s) (hu : ⋃ n, s n = Set.univ)
    (hEnv : ∀ n, MemLp T 2 (μ.restrict (s n))) (f : Lp F 2 μ) :
    Tendsto (fun n => ∫ a in s n, (T a).adjoint (f a) ∂μ) atTop
      (𝓝 ((besselAnalysis μ T hT β hβ hb).adjoint f)) := by
  have h := ((besselAnalysis μ T hT β hβ hb).adjoint.continuous.tendsto f).comp
    (l2Cutoff_tendsto μ s hs hm hu f)
  have he (n : ℕ) := besselSynthesis_cutoff_integral μ T hT β hβ hb (s n) (hs n) (hEnv n) f
  simpa only [Function.comp_def, he] using h

end VortexGap.Frame

