import VortexGap.Fermion.CountableSigns

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped InnerProduct ComplexConjugate ENNReal

theorem countableFlip_memlp (j : ℕ) (x : CountableSpace) :
    Memℓp (fun A => x (countableFlip j A)) 2 := by
  apply memℓp_gen
  exact (countableFlip j).summable_iff.mpr
    ((lp.memℓp x).summable (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal))

/-- Output-coordinate occupation mask: false annihilates, true creates. -/
def countableTransitionLinear (j : ℕ) (ε : Bool) : CountableSpace →ₗ[ℂ] CountableSpace where
  toFun x := ⟨fun A => if decide (j ∈ A) = ε then countableSign j A * x (countableFlip j A) else 0,
    (countableFlip_memlp j x).mono' (fun A => by split_ifs <;> simp [norm_mul])⟩
  map_add' x y := by
    ext A
    change (if decide (j ∈ A) = ε then countableSign j A *
      (x (countableFlip j A) + y (countableFlip j A)) else 0) =
      (if decide (j ∈ A) = ε then countableSign j A * x (countableFlip j A) else 0) +
      (if decide (j ∈ A) = ε then countableSign j A * y (countableFlip j A) else 0)
    by_cases h : decide (j ∈ A) = ε <;> simp [h, mul_add]
  map_smul' c x := by
    ext A
    by_cases h : decide (j ∈ A) = ε <;> simp [h, mul_left_comm]

theorem countableTransitionLinear_apply (j : ℕ) (ε : Bool) (x : CountableSpace) (A : Finset ℕ) :
    countableTransitionLinear j ε x A =
      if decide (j ∈ A) = ε then countableSign j A * x (countableFlip j A) else 0 := rfl

theorem countableSpace_norm_sq (x : CountableSpace) : ‖x‖ ^ 2 = ∑' A, ‖x A‖ ^ 2 := by
  simpa using lp.norm_rpow_eq_tsum (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal) x

theorem countableTransitionLinear_norm_le (j : ℕ) (ε : Bool) (x : CountableSpace) :
    ‖countableTransitionLinear j ε x‖ ≤ ‖x‖ := by
  let y : CountableSpace := ⟨fun A => x (countableFlip j A), countableFlip_memlp j x⟩
  have hsq : ‖y‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [countableSpace_norm_sq y, countableSpace_norm_sq x]
    exact (countableFlip j).tsum_eq (fun A => ‖x A‖ ^ 2)
  have hy : ‖y‖ = ‖x‖ := by nlinarith [norm_nonneg y, norm_nonneg x]
  rw [← hy]
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  intro A
  change ‖countableTransitionLinear j ε x A‖ ≤ ‖x (countableFlip j A)‖
  rw [countableTransitionLinear_apply]
  split_ifs <;> simp [norm_mul]

/-- Concrete bounded signed occupation flip on the full countable-mode Fock space. -/
def countableTransition (j : ℕ) (ε : Bool) : CountableSpace →L[ℂ] CountableSpace :=
  (countableTransitionLinear j ε).mkContinuous 1
    (fun x => by simpa using countableTransitionLinear_norm_le j ε x)

abbrev countableAnnihilateMode (j : ℕ) := countableTransition j false
abbrev countableCreateMode (j : ℕ) := countableTransition j true

theorem countableTransition_apply (j : ℕ) (ε : Bool) (x : CountableSpace) (A : Finset ℕ) :
    countableTransition j ε x A =
      if decide (j ∈ A) = ε then countableSign j A * x (countableFlip j A) else 0 := rfl

theorem countableTransition_norm_le (j : ℕ) (ε : Bool) (x : CountableSpace) :
    ‖countableTransition j ε x‖ ≤ ‖x‖ := countableTransitionLinear_norm_le j ε x

theorem countableTransition_opNorm_le (j : ℕ) (ε : Bool) :
    ‖countableTransition j ε‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [one_mul] using countableTransition_norm_le j ε x

/-- Actual Hilbert adjoint, proved by reindexing the absolutely summable inner product. -/
theorem countableTransition_adjoint (j : ℕ) (ε : Bool) :
    (countableTransition j ε).adjoint = countableTransition j (!ε) := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  rw [← (countableFlip j).tsum_eq (fun A => inner ℂ (x A) (countableTransition j ε y A))]
  apply tsum_congr
  intro A
  simp only [countableTransition_apply, countableFlip_mem_self, countableFlip_flip,
    countableSign_flip_self]
  cases ε <;> by_cases hj : j ∈ A <;>
    simp [hj, RCLike.inner_apply, map_mul] <;> ring

end VortexGap.Fermion

