import VortexGap.Operator.L2Exchange

noncomputable section
set_option autoImplicit false
namespace VortexGap
open scoped ENNReal

abbrev L2Product (α β : Type*) := lp (fun _ : α × β => ℂ) 2

/-- A row of an actual square-summable product vector. -/
def l2ProductFiber {α β : Type*} (x : L2Product α β) (a : α) :
    lp (fun _ : β => ℂ) 2 :=
  ⟨fun b => x (a,b), memℓp_gen (by
    simpa only [show (2 : ℝ≥0∞).toReal = (2 : ℝ) by norm_num, Real.rpow_two] using
      ((summable_prod_of_nonneg (fun ab => sq_nonneg ‖x ab‖)).mp
        (l2_norm_sq_summable x)).1 a)⟩

theorem l2ProductFiber_apply {α β : Type*} (x : L2Product α β) (a : α) (b : β) :
    l2ProductFiber x a b = x (a,b) := rfl

theorem l2ProductFiber_summable {α β : Type*} (x : L2Product α β) :
    Summable (fun a => ‖l2ProductFiber x a‖ ^ 2) := by
  have h := ((summable_prod_of_nonneg (fun ab => sq_nonneg ‖x ab‖)).mp
    (l2_norm_sq_summable x)).2
  exact h.congr fun a => (l2_norm_sq (l2ProductFiber x a)).symm

def l2CurryLinear (α β : Type*) : L2Product α β →ₗ[ℂ] L2Matrix α β where
  toFun x := ⟨l2ProductFiber x, memℓp_gen (by
    simpa only [show (2 : ℝ≥0∞).toReal = (2 : ℝ) by norm_num, Real.rpow_two] using
      l2ProductFiber_summable x)⟩
  map_add' x y := by ext a b; rfl
  map_smul' c x := by ext a b; rfl

def l2UncurryLinear (α β : Type*) : L2Matrix α β →ₗ[ℂ] L2Product α β where
  toFun x := ⟨fun ab => x ab.1 ab.2, memℓp_gen (by
    simpa only [show (2 : ℝ≥0∞).toReal = (2 : ℝ) by norm_num, Real.rpow_two] using
      l2_joint_norm_sq_summable x)⟩
  map_add' x y := by ext ab; rfl
  map_smul' c x := by ext ab; rfl

theorem l2CurryLinear_norm {α β : Type*} (x : L2Product α β) :
    ‖l2CurryLinear α β x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [l2_norm_sq, l2_norm_sq]
  change (∑' a, ‖l2ProductFiber x a‖ ^ 2) = ∑' ab, ‖x ab‖ ^ 2
  simp_rw [l2_norm_sq]
  exact (l2_norm_sq_summable x).tsum_prod.symm

/-- Fubini identification of completed Hilbert sums, without finite support. -/
def l2Curry (α β : Type*) : L2Product α β ≃ₗᵢ[ℂ] L2Matrix α β where
  toLinearEquiv :=
    { toLinearMap := l2CurryLinear α β
      invFun := l2UncurryLinear α β
      left_inv := by intro x; ext ab; rfl
      right_inv := by intro x; ext a b; rfl }
  norm_map' := l2CurryLinear_norm

theorem l2Curry_apply {α β : Type*} (x : L2Product α β) (a : α) (b : β) :
    l2Curry α β x a b = x (a,b) := rfl

theorem l2Curry_symm_apply {α β : Type*} (x : L2Matrix α β) (ab : α × β) :
    (l2Curry α β).symm x ab = x ab.1 ab.2 := rfl

theorem l2Product_norm_sq {α β : Type*} (x : L2Product α β) :
    ‖x‖ ^ 2 = ∑' a, ‖l2ProductFiber x a‖ ^ 2 := by
  rw [← (l2Curry α β).norm_map x, l2_norm_sq]
  rfl

theorem l2Product_inner {α β : Type*} (x y : L2Product α β) :
    inner ℂ x y = ∑' a, inner ℂ (l2ProductFiber x a) (l2ProductFiber y a) := by
  rw [← (l2Curry α β).inner_map_map x y, lp.inner_eq_tsum]
  rfl

theorem l2Curry_single {α β : Type*} [DecidableEq α] [DecidableEq β]
    (a : α) (b : β) (z : ℂ) :
    l2Curry α β (lp.single 2 (a,b) z) = lp.single 2 a (lp.single 2 b z) := by
  ext c d
  by_cases ha : a = c <;> by_cases hb : b = d <;>
    simp [l2Curry_apply, lp.single_apply, ha, hb]

end VortexGap
