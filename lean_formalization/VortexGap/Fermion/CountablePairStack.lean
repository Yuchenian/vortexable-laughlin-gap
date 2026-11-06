import VortexGap.Fermion.CountablePairBounds

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped InnerProduct ENNReal

/-- Hilbert sum of all pair-annihilation outputs; no finite mode cutoff. -/
abbrev CountablePairStackSpace := lp (fun _ : CountablePairIndex => CountableSpace) 2

def countablePairStackLinear (N : ℕ) : countableSector N →ₗ[ℂ] CountablePairStackSpace where
  toFun x := ⟨fun a => countablePairMode a x, by
    apply memℓp_gen
    simpa only [show (2 : ℝ≥0∞).toReal = (2 : ℝ) by norm_num, Real.rpow_two] using
      countablePairMode_norm_sq_summable x.property⟩
  map_add' x y := by
    ext a A
    change countablePairMode a ((x : CountableSpace) + (y : CountableSpace)) A =
      (countablePairMode a x + countablePairMode a y) A
    rw [map_add]
  map_smul' z x := by
    ext a A
    change countablePairMode a (z • (x : CountableSpace)) A = (z • countablePairMode a x) A
    rw [map_smul]

theorem countablePairStackLinear_norm_sq {N : ℕ} (x : countableSector N) :
    ‖countablePairStackLinear N x‖ ^ 2 = (N.choose 2 : ℝ) * ‖x‖ ^ 2 := by
  calc
    _ = ∑' a, ‖countablePairMode a x‖ ^ 2 := by
      simpa [countablePairStackLinear] using lp.norm_rpow_eq_tsum
        (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal) (countablePairStackLinear N x)
    _ = _ := countablePairMode_tsum_norm_sq x.property

theorem countablePairStackLinear_norm {N : ℕ} (x : countableSector N) :
    ‖countablePairStackLinear N x‖ = Real.sqrt (N.choose 2 : ℝ) * ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [countablePairStackLinear_norm_sq, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]

/-- Bounded pair analysis on each complete fixed-N sector. -/
def countablePairStack (N : ℕ) : countableSector N →L[ℂ] CountablePairStackSpace :=
  (countablePairStackLinear N).mkContinuous (Real.sqrt (N.choose 2 : ℝ))
    (fun x => le_of_eq (countablePairStackLinear_norm x))

theorem countablePairStack_apply {N : ℕ} (x : countableSector N) (a : CountablePairIndex) :
    countablePairStack N x a = countablePairMode a x := rfl

theorem countablePairStack_norm {N : ℕ} (x : countableSector N) :
    ‖countablePairStack N x‖ = Real.sqrt (N.choose 2 : ℝ) * ‖x‖ :=
  countablePairStackLinear_norm x

theorem countablePairStack_opNorm_le (N : ℕ) :
    ‖countablePairStack N‖ ≤ Real.sqrt (N.choose 2 : ℝ) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro x
  exact le_of_eq (countablePairStack_norm x)

theorem countablePairStack_opNorm_eq (N : ℕ) :
    ‖countablePairStack N‖ = Real.sqrt (N.choose 2 : ℝ) := by
  apply le_antisymm (countablePairStack_opNorm_le N)
  let x : countableSector N := ⟨countableKet (Finset.range N),
    by simpa only [Finset.card_range] using countableKet_sector (Finset.range N)⟩
  have hx : ‖x‖ = 1 := countableKet_norm _
  have h := (countablePairStack N).le_opNorm x
  simpa only [countablePairStack_norm, hx, mul_one] using h

theorem countablePairStack_component_sector {N : ℕ} (x : countableSector (N + 2))
    (a : CountablePairIndex) : countablePairStack (N + 2) x a ∈ countableSector N :=
  countablePairMode_sector a x.property

theorem countablePairStack_zero : countablePairStack 0 = 0 := by
  ext x a A
  change countablePairMode a x A = 0
  rw [countablePairMode_zero_sector a x.property]
  rfl

theorem countablePairStack_one : countablePairStack 1 = 0 := by
  ext x a A
  change countablePairMode a x A = 0
  rw [countablePairMode_one_sector a x.property]
  rfl

/-- On two particles each pair output is its coefficient times the vacuum. -/
theorem countablePairMode_pairEmbedding (a : CountablePairIndex) (p : CountablePairSpace) :
    countablePairMode a (countablePairEmbedding p) = p a • countableKet ∅ := by
  have hs := countablePairMode_sector (N := 0) a (countablePairEmbedding_sector p)
  have hc : countablePairMode a (countablePairEmbedding p) ∅ = p a := by
    rw [← countableKet_inner_left]
    rw [← ContinuousLinearMap.adjoint_inner_left]
    change inner ℂ (countablePairKet a) (countablePairEmbedding p) = _
    rw [countablePairKet_occupation, countableKet_inner_left, countablePairEmbedding_coefficient]
  ext A
  by_cases hA : A = ∅
  · subst A
    simpa [countableKet_apply] using hc
  · have hn : A.card ≠ 0 := fun h => hA (Finset.card_eq_zero.mp h)
    change countablePairMode a (countablePairEmbedding p) A = p a * countableKet ∅ A
    rw [hs A hn, countableKet_apply, if_neg hA, mul_zero]

end VortexGap.Fermion

