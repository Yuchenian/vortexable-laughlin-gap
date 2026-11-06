import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Tactic
import Mathlib.Analysis.Normed.Lp.lpHolder

noncomputable section
set_option autoImplicit false
namespace VortexGap
open scoped ENNReal

abbrev L2Matrix (α β : Type*) := lp (fun _ : α => lp (fun _ : β => ℂ) 2) 2

theorem l2_norm_sq {α E : Type*} [NormedAddCommGroup E] (z : lp (fun _ : α => E) 2) :
    ‖z‖ ^ 2 = ∑' a, ‖z a‖ ^ 2 := by
  simpa only [show (2 : ℝ≥0∞).toReal = (2 : ℝ) by norm_num, Real.rpow_two] using
    lp.norm_rpow_eq_tsum (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal) z

theorem l2_norm_sq_summable {α E : Type*} [NormedAddCommGroup E]
    (z : lp (fun _ : α => E) 2) : Summable (fun a => ‖z a‖ ^ 2) := by
  simpa only [show (2 : ℝ≥0∞).toReal = (2 : ℝ) by norm_num, Real.rpow_two] using
    (lp.memℓp z).summable (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)

/-- An actual column of a square-summable matrix. -/
def l2ExchangeFiber {α β : Type*} (z : L2Matrix α β) (b : β) : lp (fun _ : α => ℂ) 2 :=
  ⟨fun a => z a b, (lp.memℓp z).norm.mono fun a =>
    lp.norm_apply_le_norm (by norm_num) (z a) b⟩

theorem l2_joint_norm_sq_summable {α β : Type*} (z : L2Matrix α β) :
    Summable (fun ab : α × β => ‖z ab.1 ab.2‖ ^ 2) := by
  apply (summable_prod_of_nonneg (fun ab => sq_nonneg _)).mpr
  refine ⟨fun a => l2_norm_sq_summable (z a), ?_⟩
  simpa only [← l2_norm_sq] using l2_norm_sq_summable z

theorem l2ExchangeFiber_norm_sq_summable {α β : Type*} (z : L2Matrix α β) :
    Summable (fun b => ‖l2ExchangeFiber z b‖ ^ 2) := by
  have h := (l2_joint_norm_sq_summable z).prod_symm.prod
  exact h.congr fun b => (l2_norm_sq (l2ExchangeFiber z b)).symm

def l2ExchangeLinear (α β : Type*) : L2Matrix α β →ₗ[ℂ] L2Matrix β α where
  toFun z := ⟨l2ExchangeFiber z, memℓp_gen (by
    simpa only [show (2 : ℝ≥0∞).toReal = (2 : ℝ) by norm_num, Real.rpow_two] using
      l2ExchangeFiber_norm_sq_summable z)⟩
  map_add' z w := by ext b a; rfl
  map_smul' c z := by ext b a; rfl

theorem l2ExchangeLinear_norm {α β : Type*} (z : L2Matrix α β) :
    ‖l2ExchangeLinear α β z‖ = ‖z‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [l2_norm_sq, l2_norm_sq]
  change (∑' b, ‖l2ExchangeFiber z b‖ ^ 2) = ∑' a, ‖z a‖ ^ 2
  simp_rw [l2_norm_sq]
  exact (l2_joint_norm_sq_summable z).tsum_comm

/-- Exchange the two Hilbert-sum coordinates, with no finite-support assumption. -/
def l2Exchange (α β : Type*) : L2Matrix α β ≃ₗᵢ[ℂ] L2Matrix β α where
  toLinearEquiv :=
    { toLinearMap := l2ExchangeLinear α β
      invFun := l2ExchangeLinear β α
      left_inv := by intro z; ext a b; rfl
      right_inv := by intro z; ext b a; rfl }
  norm_map' := l2ExchangeLinear_norm

theorem l2Exchange_apply {α β : Type*} (z : L2Matrix α β) (b : β) (a : α) :
    l2Exchange α β z b a = z a b := rfl

theorem l2Exchange_symm_apply {α β : Type*} (z : L2Matrix β α) :
    (l2Exchange α β).symm z = l2Exchange β α z := rfl

theorem l2Exchange_involutive {α β : Type*} (z : L2Matrix α β) :
    l2Exchange β α (l2Exchange α β z) = z := (l2Exchange α β).symm_apply_apply z

end VortexGap
