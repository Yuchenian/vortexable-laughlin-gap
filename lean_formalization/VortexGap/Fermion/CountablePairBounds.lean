import VortexGap.Fermion.CountablePairCompatibility

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open Filter
open scoped InnerProduct BigOperators Topology

theorem countableRestrict_pairMode {n : ℕ} (a : PairIndex n) (x : CountableSpace) :
    countableRestrict n (countablePairMode (pairIndexNat a) x) =
      pairMode a (countableRestrict n x) := by
  change countableRestrict n (countableAnnihilateMode a.val.2.val
    (countableAnnihilateMode a.val.1.val x)) = _
  rw [countableRestrict_transition, countableRestrict_transition]
  rfl

theorem countablePairMode_partial_sum_embed_le {n N : ℕ} {y : Space n}
    (hy : InSector N y) (s : Finset CountablePairIndex)
    (hs : ∀ a ∈ s, a.val.2 < n) :
    ∑ a ∈ s, ‖countablePairMode a (countableEmbed n y)‖ ^ 2 ≤
      (N.choose 2 : ℝ) * ‖y‖ ^ 2 := by
  classical
  let e : s → PairIndex n := fun a =>
    ⟨(⟨a.val.val.1, lt_trans a.val.property (hs a.val a.property)⟩,
      ⟨a.val.val.2, hs a.val a.property⟩), a.val.property⟩
  have heNat (a : s) : pairIndexNat (e a) = a.val := rfl
  have he : Function.Injective e := by
    intro a b h
    apply Subtype.ext
    simpa only [heNat] using congrArg pairIndexNat h
  calc
    _ = ∑ a : s, ‖pairMode (e a) y‖ ^ 2 := by
      rw [← Finset.sum_coe_sort]
      apply Finset.sum_congr rfl
      intro a _
      rw [← heNat a, countablePairMode_embed, (countableEmbed n).norm_map]
    _ ≤ ∑ a : PairIndex n, ‖pairMode a y‖ ^ 2 :=
      Finset.sum_le_sum_of_injOn e he.injOn (Finset.subset_univ _)
        (by intro a ha; exact le_rfl) (by intro a ha hne; exact sq_nonneg _)
    _ = _ := sum_pairMode_norm_sq hy

/-- Uniform finite-subset bound on an arbitrary complete fixed-N state.
Finite-mode approximation is used only for this norm estimate, never to inherit a gap. -/
theorem countablePairMode_partial_sum_le {N : ℕ} {x : CountableSpace}
    (hx : x ∈ countableSector N) (s : Finset CountablePairIndex) :
    ∑ a ∈ s, ‖countablePairMode a x‖ ^ 2 ≤ (N.choose 2 : ℝ) * ‖x‖ ^ 2 := by
  have hc : Continuous (fun y : CountableSpace => ∑ a ∈ s, ‖countablePairMode a y‖ ^ 2) := by
    fun_prop
  apply le_of_tendsto ((hc.tendsto x).comp (countableEmbed_restrict_tendsto x))
  let n := s.sup (fun a => a.val.2) + 1
  filter_upwards [eventually_ge_atTop n] with m hm
  have hs : ∀ a ∈ s, a.val.2 < m := by
    intro a ha
    have h := Finset.le_sup (f := fun a : CountablePairIndex => a.val.2) ha
    dsimp [n] at hm
    omega
  calc
    _ ≤ (N.choose 2 : ℝ) * ‖countableRestrict m x‖ ^ 2 :=
      countablePairMode_partial_sum_embed_le (countableRestrict_sector hx) s hs
    _ ≤ _ := mul_le_mul_of_nonneg_left
      ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (countableRestrict_norm_le m x))
      (Nat.cast_nonneg _)

theorem countablePairMode_norm_sq_summable {N : ℕ} {x : CountableSpace}
    (hx : x ∈ countableSector N) : Summable (fun a => ‖countablePairMode a x‖ ^ 2) :=
  summable_of_sum_le (fun a => sq_nonneg _) (countablePairMode_partial_sum_le hx)

theorem countablePairMode_tsum_norm_sq_le {N : ℕ} {x : CountableSpace}
    (hx : x ∈ countableSector N) :
    ∑' a, ‖countablePairMode a x‖ ^ 2 ≤ (N.choose 2 : ℝ) * ‖x‖ ^ 2 :=
  Real.tsum_le_of_sum_le (fun a => sq_nonneg _) (countablePairMode_partial_sum_le hx)

/-- Exact pair counting for arbitrary finite N and countably many modes. -/
theorem countablePairMode_tsum_norm_sq {N : ℕ} {x : CountableSpace}
    (hx : x ∈ countableSector N) :
    ∑' a, ‖countablePairMode a x‖ ^ 2 = (N.choose 2 : ℝ) * ‖x‖ ^ 2 := by
  classical
  apply le_antisymm (countablePairMode_tsum_norm_sq_le hx)
  have hlim : Tendsto (fun n => (N.choose 2 : ℝ) *
      ‖countableEmbed n (countableRestrict n x)‖ ^ 2) atTop
      (𝓝 ((N.choose 2 : ℝ) * ‖x‖ ^ 2)) :=
    tendsto_const_nhds.mul ((countableEmbed_restrict_tendsto x).norm.pow 2)
  apply le_of_tendsto' hlim
  intro n
  rw [(countableEmbed n).norm_map, ← sum_pairMode_norm_sq (countableRestrict_sector (n := n) hx)]
  calc
    _ ≤ ∑ a : PairIndex n, ‖countablePairMode (pairIndexNat a) x‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro a ha
      rw [← countableRestrict_pairMode]
      exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (countableRestrict_norm_le _ _)
    _ = ∑ a ∈ Finset.univ.image (@pairIndexNat n), ‖countablePairMode a x‖ ^ 2 :=
      (Finset.sum_image (s := Finset.univ) (f := fun a : CountablePairIndex =>
        ‖countablePairMode a x‖ ^ 2) (pairIndexNat_injective n).injOn).symm
    _ ≤ _ := (countablePairMode_norm_sq_summable hx).sum_le_tsum _ (fun a ha => sq_nonneg _)

end VortexGap.Fermion

