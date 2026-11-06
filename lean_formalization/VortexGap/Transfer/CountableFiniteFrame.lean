import VortexGap.Fermion.CountableFramePositivity
import VortexGap.Operator.QuadraticNorm
import VortexGap.Fermion.CountableReferenceGap
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open VortexGap.Frame
open scoped BigOperators InnerProduct ComplexOrder

/-- Concrete finite-frame transfer on countably many modes, first for N+2.
Only raw frame bounds and original reference sectors enter. -/
theorem countable_finite_frame_transfer_norm_add_two {ι : Type*} [Fintype ι]
    (M : CountableOrbital →L[ℂ] CountableOrbital) (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (U : ι → CountableTwoFrame)
    (ω : ι → ℝ) (hω : ∀ i, 0 < ω i) (C : ℝ)
    (hrow : ∀ i, ∑ j, w j * traceNormTwo (countableTwoFrameOverlap (U i) (U j)) * ω j ≤ C * ω i)
    (β : ℝ) (hβ : 0 ≤ β)
    (hQ : ∀ q : CountablePairSpace,
      (inner ℂ q (countableFramePair Finset.univ (fun i => (w i : ℂ))
        (fun i => U i (PiLp.single 2 0 1)) (fun i => U i (PiLp.single 2 1 1)) q)).re ≤ β * ‖q‖^2)
    (γ : ℝ) (N : ℕ)
    (hgap : ∀ k ≤ N+2,
      (countablePairLift k (countableFramePair Finset.univ (fun i => (w i : ℂ))
        (fun i => U i (PiLp.single 2 0 1)) (fun i => U i (PiLp.single 2 1 1))) *
       countablePairLift k (countableFramePair Finset.univ (fun i => (w i : ℂ))
        (fun i => U i (PiLp.single 2 0 1)) (fun i => U i (PiLp.single 2 1 1))) -
       (γ : ℂ) • countablePairLift k (countableFramePair Finset.univ (fun i => (w i : ℂ))
        (fun i => U i (PiLp.single 2 0 1)) (fun i => U i (PiLp.single 2 1 1)))).IsPositive)
    (x : countableSector (N+2)) :
    (γ-C*‖1-M^2‖-β*‖1-M^2‖^2) *
      (inner ℂ x (countablePairLift (N+2)
        (countableFramePair Finset.univ (fun i => (w i : ℂ))
          (fun i => M (U i (PiLp.single 2 0 1)))
          (fun i => M (U i (PiLp.single 2 1 1)))) x)).re ≤
    ‖countablePairLift (N+2)
      (countableFramePair Finset.univ (fun i => (w i : ℂ))
        (fun i => M (U i (PiLp.single 2 0 1)))
        (fun i => M (U i (PiLp.single 2 1 1)))) x‖^2 := by
  let u := fun i => U i (PiLp.single 2 0 1)
  let v := fun i => U i (PiLp.single 2 1 1)
  let Q := countableFramePair Finset.univ (fun i => (w i : ℂ)) u v
  let H := countablePairLift (N+2)
    (countableFramePair Finset.univ (fun i => (w i : ℂ)) (fun i => M (u i)) (fun i => M (v i)))
  let T := countablePairLift (N+2)
    (countablePairConjugate (countableLossEmbedding M hM hc) Q)
  let V := countableFockSector countableSysOrbital (N+2)
  have hp : T.IsPositive := countablePairLift_positive _ _
    (countablePairConjugate_positive _ _ (countableFramePair_positive w hw u v))
  have hg := (quadratic_positive_norm_iff T hp γ).mp
    (countableLoss_pairLift_gap M hM hc (N+2) Q γ hgap) (V x)
  have hf : inner ℂ (V x) (T (V x)) = inner ℂ x (H x) :=
    countableLoss_frame_firstMoment Finset.univ (fun i => (w i : ℂ)) M hM hc u v x x
  have hn := countableLoss_frame_output_norm_sq Finset.univ (fun i => (w i : ℂ)) M hM hc u v x
  change ‖T (V x)‖^2 = ‖H x‖^2 +
    ‖countableFrameNoiseOne Finset.univ (fun i => (w i : ℂ)) M u v (N+2) x‖^2 +
    ‖countableFrameNoiseTwo Finset.univ (fun i => (w i : ℂ)) M u v (N+2) x‖^2 at hn
  rw [hf, hn] at hg
  have h1 := countableFrameNoiseOne_relative M hM hc w hw U ω hω C hrow (N+2) x
  have h2 := countableFrameNoiseTwo_relative M hM hc w hw u v β hβ hQ (N+2) x
  change ‖countableFrameNoiseOne Finset.univ (fun i => (w i : ℂ)) M u v (N+2) x‖^2 ≤
    C*‖1-M^2‖*(inner ℂ x (H x)).re at h1
  change ‖countableFrameNoiseTwo Finset.univ (fun i => (w i : ℂ)) M u v (N+2) x‖^2 ≤
    β*‖1-M^2‖^2*(inner ℂ x (H x)).re at h2
  change (γ-C*‖1-M^2‖-β*‖1-M^2‖^2)*(inner ℂ x (H x)).re ≤ ‖H x‖^2
  nlinarith only [hg,h1,h2]

/-- Every fixed particle sector, including the vacuum and one-particle sectors. -/
theorem countable_finite_frame_transfer_norm {ι : Type*} [Fintype ι]
    (M : CountableOrbital →L[ℂ] CountableOrbital) (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (U : ι → CountableTwoFrame)
    (ω : ι → ℝ) (hω : ∀ i, 0 < ω i) (C : ℝ)
    (hrow : ∀ i, ∑ j, w j * traceNormTwo (countableTwoFrameOverlap (U i) (U j)) * ω j ≤ C * ω i)
    (β : ℝ) (hβ : 0 ≤ β)
    (hQ : ∀ q : CountablePairSpace,
      (inner ℂ q (countableFramePair Finset.univ (fun i => (w i : ℂ))
        (fun i => U i (PiLp.single 2 0 1)) (fun i => U i (PiLp.single 2 1 1)) q)).re ≤ β * ‖q‖^2)
    (γ : ℝ) (N : ℕ)
    (hgap : ∀ k ≤ N,
      (countablePairLift k (countableFramePair Finset.univ (fun i => (w i : ℂ))
        (fun i => U i (PiLp.single 2 0 1)) (fun i => U i (PiLp.single 2 1 1))) *
       countablePairLift k (countableFramePair Finset.univ (fun i => (w i : ℂ))
        (fun i => U i (PiLp.single 2 0 1)) (fun i => U i (PiLp.single 2 1 1))) -
       (γ : ℂ) • countablePairLift k (countableFramePair Finset.univ (fun i => (w i : ℂ))
        (fun i => U i (PiLp.single 2 0 1)) (fun i => U i (PiLp.single 2 1 1)))).IsPositive)
    (x : countableSector (N)) :
    (γ-C*‖1-M^2‖-β*‖1-M^2‖^2) *
      (inner ℂ x (countablePairLift (N)
        (countableFramePair Finset.univ (fun i => (w i : ℂ))
          (fun i => M (U i (PiLp.single 2 0 1)))
          (fun i => M (U i (PiLp.single 2 1 1)))) x)).re ≤
    ‖countablePairLift (N)
      (countableFramePair Finset.univ (fun i => (w i : ℂ))
        (fun i => M (U i (PiLp.single 2 0 1)))
        (fun i => M (U i (PiLp.single 2 1 1)))) x‖^2 := by
  rcases N with _ | N
  · simp only [countablePairLift_zero_sector, ContinuousLinearMap.zero_apply, inner_zero_right,
      Complex.zero_re, mul_zero, norm_zero, zero_pow (by decide : 2 ≠ 0), le_refl]
  rcases N with _ | N
  · simp [Nat.succ_eq_add_one, countablePairLift_one_sector]
  exact countable_finite_frame_transfer_norm_add_two M hM hc w hw U ω hω C hrow
    β hβ hQ γ N hgap x

/-- Concrete operator spectral inequality: no noise or enlarged-gap hypothesis. -/
theorem countable_finite_frame_transfer {ι : Type*} [Fintype ι]
    (M : CountableOrbital →L[ℂ] CountableOrbital) (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (U : ι → CountableTwoFrame)
    (ω : ι → ℝ) (hω : ∀ i, 0 < ω i) (C : ℝ)
    (hrow : ∀ i, ∑ j, w j * traceNormTwo (countableTwoFrameOverlap (U i) (U j)) * ω j ≤ C * ω i)
    (β : ℝ) (hβ : 0 ≤ β)
    (hQ : ∀ q : CountablePairSpace,
      (inner ℂ q (countableFramePair Finset.univ (fun i => (w i : ℂ))
        (fun i => U i (PiLp.single 2 0 1)) (fun i => U i (PiLp.single 2 1 1)) q)).re ≤ β * ‖q‖^2)
    (γ : ℝ) (N : ℕ)
    (hgap : ∀ k ≤ N,
      (countablePairLift k (countableFramePair Finset.univ (fun i => (w i : ℂ))
        (fun i => U i (PiLp.single 2 0 1)) (fun i => U i (PiLp.single 2 1 1))) *
       countablePairLift k (countableFramePair Finset.univ (fun i => (w i : ℂ))
        (fun i => U i (PiLp.single 2 0 1)) (fun i => U i (PiLp.single 2 1 1))) -
       (γ : ℂ) • countablePairLift k (countableFramePair Finset.univ (fun i => (w i : ℂ))
        (fun i => U i (PiLp.single 2 0 1)) (fun i => U i (PiLp.single 2 1 1)))).IsPositive)

    : let H := countablePairLift N
        (countableFramePair Finset.univ (fun i => (w i : ℂ))
          (fun i => M (U i (PiLp.single 2 0 1)))
          (fun i => M (U i (PiLp.single 2 1 1))))
      (H*H - ((γ-C*‖1-M^2‖-β*‖1-M^2‖^2 : ℝ) : ℂ) • H).IsPositive := by
  dsimp only
  apply (quadratic_positive_norm_iff _ (countablePairLift_positive _ _
    (countableFramePair_positive w hw _ _)) _).mpr
  intro x
  exact countable_finite_frame_transfer_norm M hM hc w hw U ω hω C hrow β hβ hQ γ N hgap x
end VortexGap.Fermion
