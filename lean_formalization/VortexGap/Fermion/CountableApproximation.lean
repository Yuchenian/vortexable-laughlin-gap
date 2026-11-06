import VortexGap.Fermion.CountableTruncation

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open Filter
open scoped InnerProduct BigOperators ENNReal Topology

theorem occupationIndex_subset {n : ℕ} (A : Finset (Fin n)) :
    occupationIndex A ⊆ Finset.range n := by
  intro j hj
  obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hj
  exact Finset.mem_range.mpr i.isLt

theorem occupationIndex_exists {n : ℕ} (B : Finset ℕ) (hB : B ⊆ Finset.range n) :
    ∃ A : Finset (Fin n), occupationIndex A = B := by
  let A := Finset.univ.filter (fun i : Fin n => i.val ∈ B)
  refine ⟨A, ?_⟩
  ext j
  constructor
  · intro hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hj
    exact (Finset.mem_filter.mp hi).2
  · intro hj
    let i : Fin n := ⟨j, Finset.mem_range.mp (hB hj)⟩
    exact Finset.mem_map.mpr ⟨i, by simp [A, i, hj], rfl⟩

theorem countableEmbed_outside {n : ℕ} (x : Space n) (B : Finset ℕ)
    (hB : ¬ B ⊆ Finset.range n) : countableEmbed n x B = 0 := by
  rw [← countableKet_inner_left]
  change inner ℂ (countableKet B) (∑ A, x A • countableKet (occupationIndex A)) = 0
  simp only [inner_sum, inner_smul_right, countableKet_inner]
  apply Finset.sum_eq_zero
  intro A _
  have h : B ≠ occupationIndex A := by
    intro he
    apply hB
    rw [he]
    exact occupationIndex_subset A
  simp [h]

/-- The actual adjoint restriction, not an independently assumed projection. -/
def countableRestrict (n : ℕ) : CountableSpace →L[ℂ] Space n :=
  (countableEmbed n).toContinuousLinearMap.adjoint

theorem countableRestrict_coefficient (n : ℕ) (x : CountableSpace) (A : Finset (Fin n)) :
    countableRestrict n x A = x (occupationIndex A) := by
  calc
    _ = inner ℂ (ket A) (countableRestrict n x) := by
      simp [ket, EuclideanSpace.inner_single_left]
    _ = inner ℂ (countableEmbed n (ket A)) x :=
      ContinuousLinearMap.adjoint_inner_right (countableEmbed n).toContinuousLinearMap (ket A) x
    _ = _ := by rw [countableEmbed_ket, countableKet_inner_left]

theorem countableRestrict_embed {n : ℕ} (x : Space n) :
    countableRestrict n (countableEmbed n x) = x := by
  ext A
  rw [countableRestrict_coefficient]
  exact countableEmbedLinear_coefficient x A

/-- The finite-coordinate adjoint and isometry give precisely the proved orbital cutoff. -/
theorem countableEmbed_restrict (n : ℕ) (x : CountableSpace) :
    countableEmbed n (countableRestrict n x) = countableCutoff n x := by
  ext B
  by_cases hB : B ⊆ Finset.range n
  · obtain ⟨A, rfl⟩ := occupationIndex_exists B hB
    change countableEmbedLinear n (countableRestrict n x) (occupationIndex A) = _
    rw [countableEmbedLinear_coefficient, countableRestrict_coefficient,
      countableCutoff_coefficient, if_pos (occupationIndex_subset A)]
  · rw [countableEmbed_outside _ B hB, countableCutoff_coefficient, if_neg hB]

theorem countableRestrict_norm_le (n : ℕ) (x : CountableSpace) :
    ‖countableRestrict n x‖ ≤ ‖x‖ := by
  rw [← (countableEmbed n).norm_map, countableEmbed_restrict]
  exact countableCutoff_norm_le n x

theorem countableEmbed_restrict_tendsto (x : CountableSpace) :
    Tendsto (fun n => countableEmbed n (countableRestrict n x)) atTop (𝓝 x) := by
  simpa only [countableEmbed_restrict] using countableCutoff_tendsto x

/-- Finite-mode occupation states are dense in the full countable occupation space. -/
theorem countableEmbed_dense : Dense (⋃ n, Set.range (countableEmbed n)) := by
  intro x
  apply mem_closure_of_tendsto (countableEmbed_restrict_tendsto x)
  exact Filter.Eventually.of_forall fun n => Set.mem_iUnion.mpr ⟨n, ⟨countableRestrict n x, rfl⟩⟩

end VortexGap.Fermion

