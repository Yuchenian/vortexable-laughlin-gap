import VortexGap.Fermion.CountableSplitSectors

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped InnerProduct

def countableEnvironmentProjectionLinear (K : ℕ) : CountableSplitSpace →ₗ[ℂ] CountableSplitSpace where
  toFun x := ⟨fun AB => if AB.1.card = K then x AB else 0,
    (lp.memℓp x).mono' (fun AB => by split_ifs <;> simp)⟩
  map_add' x y := by
    ext AB
    change (if AB.1.card = K then x AB + y AB else 0) =
      (if AB.1.card = K then x AB else 0) + (if AB.1.card = K then y AB else 0)
    by_cases h : AB.1.card = K <;> simp [h]
  map_smul' c x := by
    ext AB
    by_cases h : AB.1.card = K <;> simp [h]

theorem countableEnvironmentProjectionLinear_apply (K : ℕ) (x : CountableSplitSpace)
    (AB : Finset ℕ × Finset ℕ) :
    countableEnvironmentProjectionLinear K x AB = if AB.1.card = K then x AB else 0 := rfl

theorem countableEnvironmentProjectionLinear_norm (K : ℕ) (x : CountableSplitSpace) :
    ‖countableEnvironmentProjectionLinear K x‖ ≤ ‖x‖ := by
  apply lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0)
  intro AB
  rw [countableEnvironmentProjectionLinear_apply]
  split_ifs <;> simp

def countableEnvironmentProjection (K : ℕ) : CountableSplitSpace →L[ℂ] CountableSplitSpace :=
  (countableEnvironmentProjectionLinear K).mkContinuous 1 (fun x => by
    simpa only [one_mul] using countableEnvironmentProjectionLinear_norm K x)

theorem countableEnvironmentProjection_apply (K : ℕ) (x : CountableSplitSpace)
    (AB : Finset ℕ × Finset ℕ) :
    countableEnvironmentProjection K x AB = if AB.1.card = K then x AB else 0 := rfl

theorem countableEnvironmentProjection_norm (K : ℕ) (x : CountableSplitSpace) :
    ‖countableEnvironmentProjection K x‖ ≤ ‖x‖ :=
  countableEnvironmentProjectionLinear_norm K x

theorem countableEnvironmentProjection_opNorm (K : ℕ) :
    ‖countableEnvironmentProjection K‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [one_mul] using countableEnvironmentProjection_norm K x

theorem countableEnvironmentProjection_sector (K : ℕ) (x : CountableSplitSpace) :
    countableEnvironmentProjection K x ∈ countableEnvironmentSector K := by
  intro AB hAB
  rw [countableEnvironmentProjection_apply, ite_eq_right hAB]

theorem countableEnvironmentProjection_total {N : ℕ} (K : ℕ) {x : CountableSplitSpace}
    (hx : x ∈ countableSplitSector N) :
    countableEnvironmentProjection K x ∈ countableSplitSector N := by
  intro AB hAB
  rw [countableEnvironmentProjection_apply, hx AB hAB]
  split_ifs <;> rfl

theorem countableEnvironmentProjection_of_mem {K : ℕ} {x : CountableSplitSpace}
    (hx : x ∈ countableEnvironmentSector K) : countableEnvironmentProjection K x = x := by
  ext AB
  rw [countableEnvironmentProjection_apply]
  by_cases h : AB.1.card = K
  · exact ite_eq_left h
  · rw [ite_eq_right h, hx AB h]

theorem countableEnvironmentProjection_idempotent (K : ℕ) :
    (countableEnvironmentProjection K).comp (countableEnvironmentProjection K) =
      countableEnvironmentProjection K := by
  apply ContinuousLinearMap.ext
  intro x
  exact countableEnvironmentProjection_of_mem (countableEnvironmentProjection_sector K x)

theorem countableEnvironmentProjection_adjoint (K : ℕ) :
    (countableEnvironmentProjection K).adjoint = countableEnvironmentProjection K := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro AB
  by_cases h : AB.1.card = K <;> simp only [countableEnvironmentProjection_apply, h,
    ite_true, ite_false, inner_zero_left, inner_zero_right]

theorem countableEnvironmentProjection_orthogonal (K L : ℕ) (x y : CountableSplitSpace)
    (hKL : K ≠ L) :
    inner ℂ (countableEnvironmentProjection K x) (countableEnvironmentProjection L y) = 0 :=
  countableEnvironmentSector_orthogonal (countableEnvironmentProjection_sector K x)
    (countableEnvironmentProjection_sector L y) hKL

theorem countableEnvironmentProjection_above_total {N K : ℕ} {x : CountableSplitSpace}
    (hx : x ∈ countableSplitSector N) (hNK : N < K) :
    countableEnvironmentProjection K x = 0 :=
  countableSplit_environment_too_many (countableEnvironmentProjection_total K hx)
    (countableEnvironmentProjection_sector K x) hNK

/-- Exact finite resolution by reachable environment numbers, on every complete total-N state. -/
theorem countableEnvironmentProjection_sum {N : ℕ} {x : CountableSplitSpace}
    (hx : x ∈ countableSplitSector N) :
    ∑ K ∈ Finset.range (N+1), countableEnvironmentProjection K x = x := by
  ext AB
  simp only [lp.coeFn_sum, Finset.sum_apply, countableEnvironmentProjection_apply]
  by_cases hN : AB.1.card + AB.2.card = N
  · rw [Finset.sum_eq_single AB.1.card]
    · simp
    · intro K hK hne
      simp [Ne.symm hne]
    · intro hn
      exact False.elim (hn (Finset.mem_range.mpr (by omega)))
  · rw [hx AB hN]
    simp

end VortexGap.Fermion
