import VortexGap.Fermion.CountableReferenceUpTo
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped InnerProduct ComplexOrder

theorem countableEnvironment_inner (x y : CountableSplitSpace) :
    inner ℂ x y = ∑' B : Finset ℕ,
      inner ℂ (countableEnvironmentFiber x B) (countableEnvironmentFiber y B) := by
  rw [← countableSplitExchange.inner_map_map x y, l2Product_inner]
  rfl

theorem countableEnvironmentAmplify_comp (Q R : CountableSpace →L[ℂ] CountableSpace) :
    countableEnvironmentAmplify (Q.comp R) =
      (countableEnvironmentAmplify Q).comp (countableEnvironmentAmplify R) := by
  ext x AB
  change Q (R (countableEnvironmentFiber x AB.2)) AB.1 =
    Q (countableEnvironmentFiber (countableEnvironmentAmplify R x) AB.2) AB.1
  rw [countableEnvironmentAmplify_fiber]

theorem countableEnvironmentAmplify_sub (Q R : CountableSpace →L[ℂ] CountableSpace) :
    countableEnvironmentAmplify (Q-R) =
      countableEnvironmentAmplify Q - countableEnvironmentAmplify R := by
  ext x AB
  rfl

theorem countableEnvironmentAmplify_smul (c : ℂ) (Q : CountableSpace →L[ℂ] CountableSpace) :
    countableEnvironmentAmplify (c • Q) = c • countableEnvironmentAmplify Q := by
  ext x AB
  rfl

theorem countableEnvironmentAmplify_positive (Q : CountableSpace →L[ℂ] CountableSpace)
    (hQ : Q.IsPositive) : (countableEnvironmentAmplify Q).IsPositive := by
  rw [ContinuousLinearMap.isPositive_iff]
  constructor
  · intro x y
    change inner ℂ (countableEnvironmentAmplify Q x) y =
      inner ℂ x (countableEnvironmentAmplify Q y)
    rw [countableEnvironment_inner, countableEnvironment_inner]
    apply tsum_congr
    intro B
    rw [countableEnvironmentAmplify_fiber, countableEnvironmentAmplify_fiber]
    exact hQ.isSymmetric _ _
  · intro x
    rw [countableEnvironment_inner]
    apply tsum_nonneg
    intro B
    rw [countableEnvironmentAmplify_fiber]
    exact hQ.inner_nonneg_left _

/-- The bounded reference direct sum keeps its gap after adding the actual
spectator l2 factor. Identification with the embedded pair lift is separate. -/
theorem countableEnvironmentReference_gap (N : ℕ)
    (Q : CountablePairSpace →L[ℂ] CountablePairSpace) (γ : ℝ)
    (h : ∀ k ≤ N, (countablePairLift k Q * countablePairLift k Q -
      (γ : ℂ) • countablePairLift k Q).IsPositive) :
    ((countableEnvironmentAmplify (countableReferenceUpTo N Q)).comp
      (countableEnvironmentAmplify (countableReferenceUpTo N Q)) -
      (γ : ℂ) • countableEnvironmentAmplify (countableReferenceUpTo N Q)).IsPositive := by
  have hh := countableEnvironmentAmplify_positive _
    (countableReferenceUpTo_gap N Q γ h)
  simpa only [ContinuousLinearMap.mul_def, countableEnvironmentAmplify_sub,
    countableEnvironmentAmplify_comp, countableEnvironmentAmplify_smul] using hh

theorem countableEnvironmentReference_preserves_total (N : ℕ)
    (Q : CountablePairSpace →L[ℂ] CountablePairSpace)
    {x : CountableSplitSpace} (hx : x ∈ countableSplitSector N) :
    countableEnvironmentAmplify (countableReferenceUpTo N Q) x ∈ countableSplitSector N := by
  intro AB hAB
  rcases AB with ⟨A,B⟩
  rw [countableEnvironmentAmplify_apply]
  by_cases hB : B.card ≤ N
  · let y : countableSector (N-B.card) :=
      ⟨countableEnvironmentFiber x B, countableEnvironmentFiber_sector hx B⟩
    have he := countableReferenceUpTo_apply_sector N (N-B.card) (Nat.sub_le _ _) Q y
    rw [he]
    exact (countablePairLift (N-B.card) Q y).property A (by
      change A.card + B.card ≠ N at hAB
      omega)
  · rw [countableEnvironmentFiber_above_total hx B (by omega), map_zero]
    rfl
end VortexGap.Fermion
