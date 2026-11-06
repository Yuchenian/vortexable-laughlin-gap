import VortexGap.Frame.L2Cutoff
import VortexGap.Frame.L2FiniteFiber
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
noncomputable section
set_option autoImplicit false
namespace VortexGap.Frame
open MeasureTheory Filter
open scoped InnerProduct ENNReal Topology
variable {α E : Type*} [MeasurableSpace α]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (μ : Measure α)

theorem l2_norm_sq_integrable (f : Lp E 2 μ) :
    Integrable (fun a => ‖f a‖^2) μ := by
  have h := (L2.integrable_inner (𝕜 := ℂ) f f).re
  simpa only [← norm_sq_eq_re_inner (𝕜 := ℂ)] using h

theorem l2Cutoff_error_norm_sq (s : Set α) (hs : MeasurableSet s) (f : Lp E 2 μ) :
    ‖l2Cutoff μ s hs f - f‖^2 =
      ∫ a, sᶜ.indicator (fun a => ‖f a‖^2) a ∂μ := by
  rw [l2_norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (l2Cutoff μ s hs f) f, l2Cutoff_ae μ s hs f] with a hd hc
  rw [hd]
  change ‖l2Cutoff μ s hs f a-f a‖^2 = _
  rw [hc]
  by_cases h : a ∈ s <;> simp [h]

/-- Actual strong convergence of quotient-space cutoffs, with dominated convergence
applied to the integrable squared norm. No finite total measure is assumed. -/
theorem l2Cutoff_tendsto (s : ℕ → Set α) (hs : ∀ n, MeasurableSet (s n))
    (hm : Monotone s) (hu : ⋃ n, s n = Set.univ) (f : Lp E 2 μ) :
    Tendsto (fun n => l2Cutoff μ (s n) (hs n) f) atTop (𝓝 f) := by
  have hlim : ∀ᵐ a ∂μ, Tendsto
      (fun n => (s n)ᶜ.indicator (fun a => ‖f a‖^2) a) atTop (𝓝 (0 : ℝ)) := by
    apply Eventually.of_forall
    intro a
    have hmem : a ∈ ⋃ n, s n := by rw [hu]; trivial
    obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hmem
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop n] with m hmn
    simp [hm hmn hn]
  have hi := tendsto_integral_of_dominated_convergence (fun a => ‖f a‖^2)
    (fun n => ((Lp.aestronglyMeasurable f).norm.pow 2).indicator (hs n).compl)
    (l2_norm_sq_integrable μ f)
    (fun n => Eventually.of_forall fun a => by
      by_cases h : a ∈ s n <;> simp [h, sq_nonneg])
    hlim
  have hsq : Tendsto (fun n => ‖l2Cutoff μ (s n) (hs n) f-f‖^2) atTop (𝓝 (0 : ℝ)) := by
    simpa only [l2Cutoff_error_norm_sq, integral_zero, Pi.pow_def] using hi
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have h := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hsq
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using h

theorem l2Cutoff_spanning_tendsto [SigmaFinite μ] (f : Lp E 2 μ) :
    Tendsto (fun n => l2Cutoff μ (spanningSets μ n) (measurableSet_spanningSets μ n) f)
      atTop (𝓝 f) :=
  l2Cutoff_tendsto μ _ (measurableSet_spanningSets μ) (monotone_spanningSets μ)
    (iUnion_spanningSets μ) f
end VortexGap.Frame
