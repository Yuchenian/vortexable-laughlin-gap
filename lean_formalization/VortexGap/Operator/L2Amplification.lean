import VortexGap.Operator.L2Product
import Mathlib.Analysis.InnerProductSpace.Positive

noncomputable section
set_option autoImplicit false
namespace VortexGap
open scoped ComplexOrder

/-- Apply Q in each system fiber, leaving the arbitrary spectator index unchanged. -/
def l2Amplify (α : Type*) {β : Type*}
    (Q : lp (fun _ : β => ℂ) 2 →L[ℂ] lp (fun _ : β => ℂ) 2) :
    L2Product α β →L[ℂ] L2Product α β :=
  (l2Curry α β).symm.toLinearIsometry.toContinuousLinearMap.comp
    ((lp.mapCLM 2 (fun _ : α => Q) (norm_nonneg Q) (fun _ => le_rfl)).comp
      (l2Curry α β).toLinearIsometry.toContinuousLinearMap)

theorem l2Amplify_apply {α β : Type*}
    (Q : lp (fun _ : β => ℂ) 2 →L[ℂ] lp (fun _ : β => ℂ) 2)
    (x : L2Product α β) (a : α) (b : β) :
    l2Amplify α Q x (a,b) = Q (l2ProductFiber x a) b := rfl

theorem l2Amplify_fiber {α β : Type*}
    (Q : lp (fun _ : β => ℂ) 2 →L[ℂ] lp (fun _ : β => ℂ) 2)
    (x : L2Product α β) (a : α) :
    l2ProductFiber (l2Amplify α Q x) a = Q (l2ProductFiber x a) := by
  ext b; rfl

theorem l2Amplify_norm_le {α β : Type*}
    (Q : lp (fun _ : β => ℂ) 2 →L[ℂ] lp (fun _ : β => ℂ) 2)
    (x : L2Product α β) : ‖l2Amplify α Q x‖ ≤ ‖Q‖ * ‖x‖ := by
  change ‖(l2Curry α β).symm
    (lp.mapCLM 2 (fun _ : α => Q) (norm_nonneg Q) (fun _ => le_rfl)
      (l2Curry α β x))‖ ≤ _
  rw [(l2Curry α β).symm.norm_map]
  have h := (lp.mapCLM 2 (fun _ : α => Q) (norm_nonneg Q) (fun _ => le_rfl)).le_of_opNorm_le
    (lp.norm_mapCLM_le 2 _ (norm_nonneg Q) (fun _ => le_rfl)) (l2Curry α β x)
  simpa only [(l2Curry α β).norm_map] using h

theorem l2Amplify_opNorm_le (α : Type*) {β : Type*}
    (Q : lp (fun _ : β => ℂ) 2 →L[ℂ] lp (fun _ : β => ℂ) 2) :
    ‖l2Amplify α Q‖ ≤ ‖Q‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg Q) (l2Amplify_norm_le Q)

theorem l2Amplify_add (α : Type*) {β : Type*}
    (Q R : lp (fun _ : β => ℂ) 2 →L[ℂ] lp (fun _ : β => ℂ) 2) :
    l2Amplify α (Q + R) = l2Amplify α Q + l2Amplify α R := by
  ext x ab; rfl

theorem l2Amplify_sub (α : Type*) {β : Type*}
    (Q R : lp (fun _ : β => ℂ) 2 →L[ℂ] lp (fun _ : β => ℂ) 2) :
    l2Amplify α (Q - R) = l2Amplify α Q - l2Amplify α R := by
  ext x ab; rfl

theorem l2Amplify_smul (α : Type*) {β : Type*} (c : ℂ)
    (Q : lp (fun _ : β => ℂ) 2 →L[ℂ] lp (fun _ : β => ℂ) 2) :
    l2Amplify α (c • Q) = c • l2Amplify α Q := by
  ext x ab; rfl

theorem l2Amplify_zero (α β : Type*) :
    l2Amplify α (0 : lp (fun _ : β => ℂ) 2 →L[ℂ] lp (fun _ : β => ℂ) 2) = 0 := by
  ext x ab; rfl

theorem l2Amplify_one (α β : Type*) :
    l2Amplify α (1 : lp (fun _ : β => ℂ) 2 →L[ℂ] lp (fun _ : β => ℂ) 2) = 1 := by
  ext x ab; rfl

theorem l2Amplify_comp (α : Type*) {β : Type*}
    (Q R : lp (fun _ : β => ℂ) 2 →L[ℂ] lp (fun _ : β => ℂ) 2) :
    l2Amplify α (Q.comp R) = (l2Amplify α Q).comp (l2Amplify α R) := by
  ext x ab
  change Q (R (l2ProductFiber x ab.1)) ab.2 =
    Q (l2ProductFiber (l2Amplify α R x) ab.1) ab.2
  rw [l2Amplify_fiber]

theorem l2Amplify_adjoint (α : Type*) {β : Type*}
    (Q : lp (fun _ : β => ℂ) 2 →L[ℂ] lp (fun _ : β => ℂ) 2) :
    (l2Amplify α Q).adjoint = l2Amplify α Q.adjoint := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [l2Product_inner, l2Product_inner]
  apply tsum_congr
  intro a
  rw [l2Amplify_fiber, l2Amplify_fiber, ContinuousLinearMap.adjoint_inner_left]

theorem l2Amplify_positive (α : Type*) {β : Type*}
    (Q : lp (fun _ : β => ℂ) 2 →L[ℂ] lp (fun _ : β => ℂ) 2)
    (hQ : Q.IsPositive) : (l2Amplify α Q).IsPositive := by
  rw [ContinuousLinearMap.isPositive_iff]
  constructor
  · intro x y
    change inner ℂ (l2Amplify α Q x) y = inner ℂ x (l2Amplify α Q y)
    rw [l2Product_inner, l2Product_inner]
    apply tsum_congr
    intro a
    rw [l2Amplify_fiber, l2Amplify_fiber]
    exact hQ.isSymmetric _ _
  · intro x
    rw [l2Product_inner]
    apply tsum_nonneg
    intro a
    rw [l2Amplify_fiber]
    exact hQ.inner_nonneg_left _

/-- A bounded reference inequality survives an actual spectator amplification.
This is an operator lemma, not the many-body loss-transfer theorem. -/
theorem l2Amplify_quadratic_positive (α : Type*) {β : Type*}
    (Q : lp (fun _ : β => ℂ) 2 →L[ℂ] lp (fun _ : β => ℂ) 2)
    (γ : ℝ) (h : (Q.comp Q - (γ : ℂ) • Q).IsPositive) :
    ((l2Amplify α Q).comp (l2Amplify α Q) - (γ : ℂ) • l2Amplify α Q).IsPositive := by
  simpa only [l2Amplify_sub, l2Amplify_comp, l2Amplify_smul] using
    l2Amplify_positive α _ h

theorem l2Amplify_single_row {α β : Type*} [DecidableEq α]
    (Q : lp (fun _ : β => ℂ) 2 →L[ℂ] lp (fun _ : β => ℂ) 2)
    (a : α) (v : lp (fun _ : β => ℂ) 2) :
    l2Amplify α Q ((l2Curry α β).symm (lp.single 2 a v)) =
      (l2Curry α β).symm (lp.single 2 a (Q v)) := by
  ext ab
  change Q (l2ProductFiber ((l2Curry α β).symm (lp.single 2 a v)) ab.1) ab.2 =
    (lp.single 2 a (Q v) : L2Matrix α β) ab.1 ab.2
  have hf : l2ProductFiber ((l2Curry α β).symm (lp.single 2 a v)) ab.1 =
      (lp.single 2 a v : L2Matrix α β) ab.1 := by ext b; rfl
  rw [hf]
  by_cases h : a = ab.1 <;> simp [lp.single_apply, h]

end VortexGap
