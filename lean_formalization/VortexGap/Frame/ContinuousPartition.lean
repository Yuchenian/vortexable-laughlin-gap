import VortexGap.Frame.ContinuousPairLift

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory
open scoped ENNReal BigOperators

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {n : ℕ}

/-- Finite families on finite measures satisfy the controlled L2 hypothesis automatically. -/
theorem finitePair_memLp [Fintype β] [MeasurableSingletonClass β]
    (ν : Measure β) [IsFiniteMeasure ν] (p : β → PairSpace n) : MemLp p 2 ν := by
  apply MemLp.of_bound (measurable_of_finite p).aestronglyMeasurable (∑ i, ‖p i‖)
  exact Filter.Eventually.of_forall fun i =>
    Finset.single_le_sum (fun j _ => norm_nonneg (p j)) (Finset.mem_univ i)

theorem continuousPairOperator_map (μ : Measure α) (c : α → β) (hc : AEMeasurable c μ)
    (p : β → PairSpace n) (hp : MemLp p 2 (Measure.map c μ)) :
    continuousPairOperator (Measure.map c μ) p = continuousPairOperator μ (fun a => p (c a)) := by
  exact integral_map hc (continuousPairOperator_integrable (Measure.map c μ) p hp).aestronglyMeasurable

theorem continuousFrameHamiltonian_map (μ : Measure α) (c : α → β) (hc : AEMeasurable c μ)
    (p : β → PairSpace n) (hp : MemLp p 2 (Measure.map c μ)) :
    continuousFrameHamiltonian (Measure.map c μ) p =
      continuousFrameHamiltonian μ (fun a => p (c a)) := by
  exact integral_map hc (continuousFrame_integrable (Measure.map c μ) p hp).aestronglyMeasurable

/-- A measurable finite partition gives exactly the former weighted CAR Hamiltonian,
with each weight equal to the measure of its fiber. No integration identity is assumed. -/
theorem continuousFrameHamiltonian_partition [Fintype β] [MeasurableSingletonClass β]
    (μ : Measure α) [IsFiniteMeasure μ] (c : α → β) (hc : AEMeasurable c μ)
    (p : β → PairSpace n) :
    continuousFrameHamiltonian μ (fun a => p (c a)) =
      LinearMap.toContinuousLinearMap (frameHamiltonian (fun i => μ.real {a | c a = i}) p) := by
  have hp := finitePair_memLp (Measure.map c μ) p
  rw [← continuousFrameHamiltonian_map μ c hc p hp,
    continuousFrameHamiltonian_finite (Measure.map c μ) p hp]
  have hw : (fun i => (Measure.map c μ).real {i}) = fun i => μ.real {a | c a = i} := by
    funext i
    rw [measureReal_def, Measure.map_apply_of_aemeasurable hc (measurableSet_singleton i)]
    rfl
  rw [hw]

end VortexGap.Fermion
