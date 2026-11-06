import VortexGap.Examples.ContinuousPhase
import VortexGap.Examples.Cells
import VortexGap.Frame.ContinuousPartition
import Mathlib.MeasureTheory.Measure.Prod

noncomputable section
set_option autoImplicit false
namespace VortexGap.Examples
open VortexGap.Fermion VortexGap.Frame MeasureTheory
open scoped InnerProduct BigOperators ENNReal

/-- A separate Lebesgue interval of mass one for every two-mode cell. -/
def continuousCellMeasure (k : ℕ) : Measure (Fin k × ℝ) :=
  (Measure.count : Measure (Fin k)).prod phaseMeasure

instance (k : ℕ) : IsFiniteMeasure (continuousCellMeasure k) := by
  unfold continuousCellMeasure
  infer_instance

theorem continuousCellMeasure_map (k : ℕ) :
    Measure.map Prod.fst (continuousCellMeasure k) = Measure.count := by
  simp [continuousCellMeasure, Measure.map_fst_prod, phaseMeasure, Real.volume_Icc]

theorem continuousCell_integral {k : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (f : Fin k → E) :
    (∫ a, f a.1 ∂continuousCellMeasure k) = ∑ j, f j := by
  rw [← integral_map measurable_fst.aemeasurable (measurable_of_finite f).aestronglyMeasurable,
    continuousCellMeasure_map, integral_count]

theorem continuousCell_hamiltonian {k n : ℕ} (p : Fin k → PairSpace n) :
    continuousFrameHamiltonian (continuousCellMeasure k) (fun a => p a.1) =
      LinearMap.toContinuousLinearMap (frameHamiltonian (fun _ => 1) p) := by
  have hp := finitePair_memLp (Measure.map Prod.fst (continuousCellMeasure k)) p
  rw [← continuousFrameHamiltonian_map (continuousCellMeasure k) Prod.fst
    measurable_fst.aemeasurable p hp, continuousFrameHamiltonian_finite _ p hp]
  simp [continuousCellMeasure_map, measureReal_def]

theorem continuousCell_pairOperator {k n : ℕ} (p : Fin k → PairSpace n) :
    continuousPairOperator (continuousCellMeasure k) (fun a => p a.1) =
      LinearMap.toContinuousLinearMap (∑ j, pairRankOne (p j)) := by
  haveI : CompleteSpace (PairSpace n) := PiLp.completeSpace 2 (fun _ => ℂ)
  haveI : CompleteSpace (PairSpace n →L[ℂ] PairSpace n) := ContinuousLinearMap.instCompleteSpace
  have hp := finitePair_memLp (Measure.map Prod.fst (continuousCellMeasure k)) p
  rw [← continuousPairOperator_map (continuousCellMeasure k) Prod.fst
    measurable_fst.aemeasurable p hp, continuousCellMeasure_map, continuousPairOperator, integral_count]
  ext q
  simp [LinearMap.sum_apply, pairRankOne]

theorem continuousCell_column_measurable (k : ℕ) (i : Fin 2) :
    AEStronglyMeasurable (fun a : Fin k × ℝ => cellFrames k a.1 (PiLp.single 2 i 1))
      (continuousCellMeasure k) :=
  ((measurable_of_finite (fun j => cellFrames k j (PiLp.single 2 i 1))).comp
    measurable_fst).aestronglyMeasurable

theorem continuousCell_row_integrable (k : ℕ) (a : Fin k × ℝ) :
    Integrable (fun b => traceNormTwo (twoFrameOverlap (cellFrames k a.1) (cellFrames k b.1)))
      (continuousCellMeasure k) := by
  have h : Integrable (fun j => traceNormTwo (twoFrameOverlap (cellFrames k a.1) (cellFrames k j)))
      (Measure.map Prod.fst (continuousCellMeasure k)) := by
    rw [continuousCellMeasure_map]
    exact integrable_count_iff.mpr (hasSum_fintype _).summable
  exact h.comp_measurable measurable_fst

theorem continuousCell_row (k : ℕ) (a : Fin k × ℝ) :
    (∫ b, traceNormTwo (twoFrameOverlap (cellFrames k a.1) (cellFrames k b.1))
      ∂continuousCellMeasure k) = 2 := by
  rw [continuousCell_integral (fun j => traceNormTwo (twoFrameOverlap (cellFrames k a.1) (cellFrames k j)))]
  exact cell_schur k a.1

end VortexGap.Examples

