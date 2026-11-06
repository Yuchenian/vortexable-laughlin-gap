import VortexGap.Operator.L2Exchange
import VortexGap.Fermion.CountablePairAnnihilation

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped InnerProduct ComplexOrder

def countablePairFiber (z : CountablePairStackSpace) (A : Finset ℕ) : CountablePairSpace :=
  l2Exchange CountablePairIndex (Finset ℕ) z A

theorem countablePairFiber_apply (z : CountablePairStackSpace) (A : Finset ℕ)
    (a : CountablePairIndex) : countablePairFiber z A a = z a A := rfl

theorem countablePairStackSpace_norm_sq (z : CountablePairStackSpace) :
    ‖z‖ ^ 2 = ∑' A, ‖countablePairFiber z A‖ ^ 2 := by
  rw [← (l2Exchange CountablePairIndex (Finset ℕ)).norm_map z, l2_norm_sq]
  rfl

theorem countablePairStack_inner_fibers (z w : CountablePairStackSpace) :
    inner ℂ z w = ∑' A, inner ℂ (countablePairFiber z A) (countablePairFiber w A) := by
  rw [← (l2Exchange CountablePairIndex (Finset ℕ)).inner_map_map z w, lp.inner_eq_tsum]
  rfl

/-- Q acts on pair coordinates, leaving the remaining occupation coordinate unchanged. -/
def countablePairAmplify (Q : CountablePairSpace →L[ℂ] CountablePairSpace) :
    CountablePairStackSpace →L[ℂ] CountablePairStackSpace :=
  (l2Exchange CountablePairIndex (Finset ℕ)).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((lp.mapCLM 2 (fun _ : Finset ℕ => Q) (norm_nonneg Q) (fun _ => le_rfl)).comp
      (l2Exchange CountablePairIndex (Finset ℕ)).toContinuousLinearEquiv.toContinuousLinearMap)

theorem countablePairAmplify_apply (Q : CountablePairSpace →L[ℂ] CountablePairSpace)
    (z : CountablePairStackSpace) (a : CountablePairIndex) (A : Finset ℕ) :
    countablePairAmplify Q z a A = Q (countablePairFiber z A) a := rfl

theorem countablePairAmplify_fiber (Q : CountablePairSpace →L[ℂ] CountablePairSpace)
    (z : CountablePairStackSpace) (A : Finset ℕ) :
    countablePairFiber (countablePairAmplify Q z) A = Q (countablePairFiber z A) := by
  ext a
  rfl

theorem countablePairAmplify_norm_le (Q : CountablePairSpace →L[ℂ] CountablePairSpace)
    (z : CountablePairStackSpace) : ‖countablePairAmplify Q z‖ ≤ ‖Q‖ * ‖z‖ := by
  change ‖(l2Exchange CountablePairIndex (Finset ℕ)).symm
    (lp.mapCLM 2 (fun _ : Finset ℕ => Q) (norm_nonneg Q) (fun _ => le_rfl)
      (l2Exchange CountablePairIndex (Finset ℕ) z))‖ ≤ _
  rw [(l2Exchange CountablePairIndex (Finset ℕ)).symm.norm_map]
  have h := (lp.mapCLM 2 (fun _ : Finset ℕ => Q) (norm_nonneg Q) (fun _ => le_rfl)).le_of_opNorm_le
    (lp.norm_mapCLM_le 2 _ (norm_nonneg Q) (fun _ => le_rfl))
      (l2Exchange CountablePairIndex (Finset ℕ) z)
  simpa only [(l2Exchange CountablePairIndex (Finset ℕ)).norm_map] using h

theorem countablePairAmplify_opNorm_le (Q : CountablePairSpace →L[ℂ] CountablePairSpace) :
    ‖countablePairAmplify Q‖ ≤ ‖Q‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg Q) (countablePairAmplify_norm_le Q)

theorem countablePairAmplify_add (Q R : CountablePairSpace →L[ℂ] CountablePairSpace) :
    countablePairAmplify (Q + R) = countablePairAmplify Q + countablePairAmplify R := by
  ext z a A
  rfl

theorem countablePairAmplify_smul (c : ℂ) (Q : CountablePairSpace →L[ℂ] CountablePairSpace) :
    countablePairAmplify (c • Q) = c • countablePairAmplify Q := by
  ext z a A
  rfl

theorem countablePairAmplify_zero : countablePairAmplify 0 = 0 := by
  ext z a A
  rfl

theorem countablePairAmplify_one : countablePairAmplify 1 = 1 := by
  ext z a A
  rfl

theorem countablePairAmplify_comp (Q R : CountablePairSpace →L[ℂ] CountablePairSpace) :
    countablePairAmplify (Q.comp R) = (countablePairAmplify Q).comp (countablePairAmplify R) := by
  ext z a A
  change Q (R (countablePairFiber z A)) a = Q (countablePairFiber (countablePairAmplify R z) A) a
  rw [countablePairAmplify_fiber]

theorem countablePairAmplify_adjoint (Q : CountablePairSpace →L[ℂ] CountablePairSpace) :
    (countablePairAmplify Q).adjoint = countablePairAmplify Q.adjoint := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro z w
  rw [countablePairStack_inner_fibers, countablePairStack_inner_fibers]
  apply tsum_congr
  intro A
  rw [countablePairAmplify_fiber, countablePairAmplify_fiber,
    ContinuousLinearMap.adjoint_inner_left]

theorem countablePairAmplify_positive (Q : CountablePairSpace →L[ℂ] CountablePairSpace)
    (hQ : Q.IsPositive) : (countablePairAmplify Q).IsPositive := by
  rw [ContinuousLinearMap.isPositive_iff]
  constructor
  · intro z w
    change inner ℂ (countablePairAmplify Q z) w = inner ℂ z (countablePairAmplify Q w)
    rw [countablePairStack_inner_fibers, countablePairStack_inner_fibers]
    apply tsum_congr
    intro A
    rw [countablePairAmplify_fiber, countablePairAmplify_fiber]
    exact hQ.isSymmetric _ _
  · intro z
    rw [countablePairStack_inner_fibers]
    apply tsum_nonneg
    intro A
    rw [countablePairAmplify_fiber]
    exact hQ.inner_nonneg_left _

end VortexGap.Fermion
