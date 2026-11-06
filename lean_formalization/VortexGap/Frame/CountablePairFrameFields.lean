import VortexGap.Frame.CountableOneFrameFields
import VortexGap.Frame.CountableTwoFrameOverlap
import VortexGap.Fermion.CountableWedgeLinear
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory
open scoped InnerProduct ENNReal

theorem countableWedge_continuous :
    Continuous (fun z : CountableOrbital × CountableOrbital => countableWedge z.1 z.2) := by
  exact countablePairCoordinates.continuous.comp
    ((countableCreate.continuous.comp continuous_fst).clm_apply
      ((countableCreate.continuous.comp continuous_snd).clm_apply continuous_const))

theorem countableWedge_norm_le (u v : CountableOrbital) :
    ‖countableWedge u v‖ ≤ ‖u‖ * ‖v‖ := by
  rw [← countablePairEmbedding.norm_map, countableWedge_embed]
  calc
    _ ≤ ‖u‖ * ‖countableCreate v (countableKet ∅)‖ := countableCreate_norm_le _ _
    _ ≤ ‖u‖ * (‖v‖ * ‖countableKet ∅‖) :=
      mul_le_mul_of_nonneg_left (countableCreate_norm_le _ _) (norm_nonneg _)
    _ = _ := by rw [countableKet_norm, mul_one]

theorem countableWedge_memLp {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (u v : α → CountableOrbital)
    (hu : AEStronglyMeasurable u μ) (hv : AEStronglyMeasurable v μ)
    (hun : ∀ a, ‖u a‖ ≤ 1) (hvn : ∀ a, ‖v a‖ ≤ 1) :
    MemLp (fun a => countableWedge (u a) (v a)) 2 μ := by
  apply MemLp.of_bound (countableWedge_continuous.comp_aestronglyMeasurable (hu.prodMk hv)) 1
  exact Filter.Eventually.of_forall fun a =>
    (countableWedge_norm_le (u a) (v a)).trans
      ((mul_le_mul (hun a) (hvn a) (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1))

/-- The actual normalized pair carried by an orthonormal two-frame. -/
def countableTwoFramePair (U : CountableTwoFrame) : CountablePairSpace :=
  countableWedge (U (PiLp.single 2 0 1)) (U (PiLp.single 2 1 1))

theorem countableTwoFramePair_memLp {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (U : α → CountableTwoFrame)
    (hU0 : AEStronglyMeasurable (fun a => U a (PiLp.single 2 0 1)) μ)
    (hU1 : AEStronglyMeasurable (fun a => U a (PiLp.single 2 1 1)) μ) :
    MemLp (fun a => countableTwoFramePair (U a)) 2 μ :=
  countableWedge_memLp μ _ _ hU0 hU1 (fun a => by simp) (fun a => by simp)

theorem countableTwoFramePair_spanning_memLp {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [SigmaFinite μ] (U : α → CountableTwoFrame)
    (hU0 : AEStronglyMeasurable (fun a => U a (PiLp.single 2 0 1)) μ)
    (hU1 : AEStronglyMeasurable (fun a => U a (PiLp.single 2 1 1)) μ) (n : ℕ) :
    MemLp (fun a => countableTwoFramePair (U a)) 2 (μ.restrict (spanningSets μ n)) := by
  haveI : IsFiniteMeasure (μ.restrict (spanningSets μ n)) :=
    isFiniteMeasure_restrict.mpr (measure_spanningSets_lt_top μ n).ne
  exact countableTwoFramePair_memLp _ U hU0.restrict hU1.restrict

end VortexGap.Fermion
