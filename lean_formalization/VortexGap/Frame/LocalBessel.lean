import VortexGap.Frame.BesselAnalysis
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

noncomputable section
set_option autoImplicit false
namespace VortexGap.Frame
open MeasureTheory Filter
open scoped ENNReal Topology
variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
  (μ : Measure α) (s : ℕ → Set α) (hc : AECover μ atTop s)

include hc in
/-- Local L2 control on an exhausting cover yields global L2 integrability.
The uniform bound is on each vector, not on the operator-norm envelope. -/
theorem localL2_memLp (f : α → E)
    (hf : ∀ n, MemLp f 2 (μ.restrict (s n))) (K : ℝ)
    (hb : ∀ n, (∫ a in s n, ‖f a‖^2 ∂μ) ≤ K) : MemLp f 2 μ := by
  have hm : AEStronglyMeasurable f μ :=
    hc.aestronglyMeasurable (fun n => (hf n).aestronglyMeasurable)
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  exact hc.integrable_of_integral_bounded_of_nonneg_ae K
    (fun n => (memLp_two_iff_integrable_sq_norm (hf n).aestronglyMeasurable).mp (hf n))
    (Eventually.of_forall fun a => sq_nonneg ‖f a‖) (Eventually.of_forall hb)

include hc in
theorem localL2_integral_le (f : α → E)
    (hf : ∀ n, MemLp f 2 (μ.restrict (s n))) (K : ℝ)
    (hb : ∀ n, (∫ a in s n, ‖f a‖^2 ∂μ) ≤ K) :
    (∫ a, ‖f a‖^2 ∂μ) ≤ K := by
  have h := localL2_memLp μ s hc f hf K hb
  have hi := (memLp_two_iff_integrable_sq_norm h.aestronglyMeasurable).mp h
  exact le_of_tendsto (hc.integral_tendsto_of_countably_generated hi)
    (Eventually.of_forall hb)

/-- The exhaustion needed above follows from ordinary increasing measurable cutoffs. -/
theorem increasingCutoffs_aecover (hs : ∀ n, MeasurableSet (s n))
    (hm : Monotone s) (hu : ⋃ n, s n = Set.univ) : AECover μ atTop s where
  measurableSet := hs
  ae_eventually_mem := Eventually.of_forall fun a => by
    have ha : a ∈ ⋃ n, s n := by rw [hu]; trivial
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp ha
    exact (eventually_ge_atTop n).mono fun m hmn => hm hmn hn

end VortexGap.Frame

