import VortexGap.Fermion.CountableSpace
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Order.Filter.AtTopBot.Finset

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open Filter
open scoped InnerProduct BigOperators ENNReal Topology

/-- Projection onto a finite set of actual occupation configurations. -/
def countableTruncate (s : Finset (Finset ℕ)) : CountableSpace →L[ℂ] CountableSpace :=
  ∑ A ∈ s, InnerProductSpace.rankOne ℂ (countableKet A) (countableKet A)

theorem countableTruncate_apply (s : Finset (Finset ℕ)) (x : CountableSpace) :
    countableTruncate s x = ∑ A ∈ s, x A • countableKet A := by
  simp [countableTruncate, InnerProductSpace.rankOne_apply, countableKet_inner_left]

theorem countableTruncate_coefficient (s : Finset (Finset ℕ)) (x : CountableSpace) (A : Finset ℕ) :
    countableTruncate s x A = if A ∈ s then x A else 0 := by
  rw [← countableKet_inner_left, countableTruncate_apply]
  simp [inner_sum, inner_smul_right, countableKet_inner]

theorem countableTruncate_norm_sq (s : Finset (Finset ℕ)) (x : CountableSpace) :
    ‖countableTruncate s x‖^2 = ∑ A ∈ s, ‖x A‖^2 := by
  rw [countableTruncate_apply]
  simpa [countableKet, ← lp.single_smul] using
    lp.norm_sum_single (p := (2 : ℝ≥0∞)) (by norm_num) (fun A => x A) s

theorem countableTruncate_norm_le (s : Finset (Finset ℕ)) (x : CountableSpace) :
    ‖countableTruncate s x‖ ≤ ‖x‖ := by
  have hs : Summable (fun A => ‖x A‖^2) := by
    simpa using (lp.memℓp x).summable (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)
  have hn : ‖x‖^2 = ∑' A, ‖x A‖^2 := by
    simpa using lp.norm_rpow_eq_tsum (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal) x
  have h := hs.sum_le_tsum s (fun A _ => sq_nonneg ‖x A‖)
  rw [← countableTruncate_norm_sq, ← hn] at h
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

theorem countableTruncate_idempotent (s : Finset (Finset ℕ)) (x : CountableSpace) :
    countableTruncate s (countableTruncate s x) = countableTruncate s x := by
  ext A
  simp only [countableTruncate_coefficient]
  split_ifs <;> rfl

theorem countableTruncate_adjoint (s : Finset (Finset ℕ)) :
    (countableTruncate s).adjoint = countableTruncate s := by
  simp [countableTruncate, map_sum, InnerProductSpace.adjoint_rankOne]

theorem countableTruncate_tendsto (x : CountableSpace) :
    Tendsto (fun s => countableTruncate s x) atTop (𝓝 x) := by
  simpa only [countableTruncate_apply, HasSum, SummationFilter.unconditional_filter] using countableSpace_hasSum x

/-- Orbital cutoff, retaining all occupations of the first n modes, including the top sector. -/
def countableCutoff (n : ℕ) : CountableSpace →L[ℂ] CountableSpace :=
  countableTruncate (Finset.range n).powerset

theorem countableCutoff_coefficient (n : ℕ) (x : CountableSpace) (A : Finset ℕ) :
    countableCutoff n x A = if A ⊆ Finset.range n then x A else 0 := by
  simp [countableCutoff, countableTruncate_coefficient]

theorem countableCutoff_norm_le (n : ℕ) (x : CountableSpace) :
    ‖countableCutoff n x‖ ≤ ‖x‖ := countableTruncate_norm_le _ x

/-- Strong convergence on the entire countable occupation Hilbert space. -/
theorem countableCutoff_tendsto (x : CountableSpace) :
    Tendsto (fun n => countableCutoff n x) atTop (𝓝 x) :=
  (countableTruncate_tendsto x).comp
    (tendsto_finset_powerset_atTop_atTop.comp tendsto_finset_range)

end VortexGap.Fermion

