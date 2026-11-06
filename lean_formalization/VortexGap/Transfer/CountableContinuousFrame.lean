import VortexGap.Fermion.CountableContinuousLossOutput
import VortexGap.Fermion.CountableReferenceGap
import VortexGap.Fermion.CountableFramePositivity
import VortexGap.Operator.QuadraticNorm
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory Filter VortexGap.Frame
open scoped InnerProduct ENNReal ComplexOrder
variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ]
  (p : α → CountablePairSpace)
  (hp : ∀ q, MemLp (fun a => inner ℂ (p a) q) 2 μ)
  (β : ℝ) (hβ : 0 ≤ β)
  (hb : ∀ q, (∫ a, ‖inner ℂ (p a) q‖^2 ∂μ) ≤ β * ‖q‖^2)
  (hcov : AECover μ atTop (spanningSets μ))
  (hloc : ∀ n, MemLp p 2 (μ.restrict (spanningSets μ n)))
  (M : CountableOrbital →L[ℂ] CountableOrbital) (hM : 0 ≤ M) (hMc : ‖M‖ ≤ 1)
  (U : α → CountableTwoFrame)
  (hU0 : AEStronglyMeasurable (fun a => U a (PiLp.single 2 0 1)) μ)
  (hU1 : AEStronglyMeasurable (fun a => U a (PiLp.single 2 1 1)) μ)
  (hpw : ∀ a, p a = countableWedge (U a (PiLp.single 2 0 1)) (U a (PiLp.single 2 1 1)))
  (ω : α → ℝ) (hω : ∀ a, 0 < ω a) (hωm : AEStronglyMeasurable ω μ)
  (C : ℝ) (hC : 0 ≤ C)
  (hrowInt : ∀ᵐ a ∂μ, Integrable
    (fun b => traceNormTwo (countableTwoFrameOverlap (U a) (U b)) * ω b) μ)
  (hrow : ∀ᵐ a ∂μ,
    (∫ b, traceNormTwo (countableTwoFrameOverlap (U a) (U b)) * ω b ∂μ) ≤ C * ω a)

include hMc in
theorem countableContinuousFilteredHamiltonian_positive (N : ℕ) :
    (countableContinuousFilteredHamiltonian μ p hp β hβ hb M hM N).IsPositive := by
  unfold countableContinuousFilteredHamiltonian
  rw [← countableFilteredPair_operator μ p hp β hβ hb
    (countablePairFilter M hM) (countablePairFilter_contract M hM hMc)]
  exact countablePairLift_positive N _ (countableContinuousPairOperator_positive μ _ _ _ _ _)

theorem countableContinuousDilatedHamiltonian_positive (N : ℕ) :
    (countableContinuousDilatedHamiltonian μ p hp β hβ hb M hM hMc N).IsPositive :=
  countablePairLift_positive N _ (countablePairConjugate_positive _ _
    (countableContinuousPairOperator_positive μ p hp β hβ hb))

include hMc hcov hloc hU0 hU1 hpw hω hωm hC hrowInt hrow in
/-- Concrete continuous-frame transfer; the enlarged reference gap and both noises are derived. -/
theorem countable_continuous_transfer_norm_add_two (γ : ℝ) (N : ℕ)
    (hgap : ∀ k ≤ N+2,
      (countablePairLift k (countableContinuousPairOperator μ p hp β hβ hb) *
        countablePairLift k (countableContinuousPairOperator μ p hp β hβ hb) -
        (γ : ℂ) • countablePairLift k (countableContinuousPairOperator μ p hp β hβ hb)).IsPositive)
    (x : countableSector (N+2)) :
    (γ-C*‖1-M^2‖-β*‖1-M^2‖^2) *
      (inner ℂ x (countableContinuousFilteredHamiltonian μ p hp β hβ hb M hM (N+2) x)).re ≤
      ‖countableContinuousFilteredHamiltonian μ p hp β hβ hb M hM (N+2) x‖^2 := by
  let H := countableContinuousFilteredHamiltonian μ p hp β hβ hb M hM (N+2)
  let T := countableContinuousDilatedHamiltonian μ p hp β hβ hb M hM hMc (N+2)
  let V := countableFockSector countableSysOrbital (N+2)
  have hg := (quadratic_positive_norm_iff T
    (countableContinuousDilatedHamiltonian_positive μ p hp β hβ hb M hM hMc (N+2)) γ).mp
    (countableLoss_pairLift_gap M hM hMc (N+2)
      (countableContinuousPairOperator μ p hp β hβ hb) γ hgap) (V x)
  have hf := countableContinuousLoss_firstMoment μ p hp β hβ hb hcov hloc M hM hMc
    U hU0 hU1 hpw ω hω hωm C hC hrowInt hrow N x x
  have hn := countableContinuousLoss_output_norm_sq μ p hp β hβ hb hcov hloc M hM hMc
    U hU0 hU1 hpw ω hω hωm C hC hrowInt hrow N x
  rw [hf, hn] at hg
  have h1 := countableContinuousNoiseOne_relative μ p hp β hβ hb (spanningSets μ) hcov hloc
    M hM hMc U hU0 hU1 ω hω hωm C hC hrowInt hrow
    (monotone_spanningSets μ) (iUnion_spanningSets μ) (N+2) x
  have h2 := countableContinuousNoiseTwo_relative μ p hp β hβ hb (spanningSets μ) hcov hloc
    M hM hMc (monotone_spanningSets μ) (iUnion_spanningSets μ) (N+2) x
  change ‖countableContinuousNoiseOne μ p hp β hβ hb (spanningSets μ) hcov hloc
    M hM hMc U hU0 hU1 ω hω hωm C hC hrowInt hrow (N+2) x‖^2 ≤
    C*‖1-M^2‖*(inner ℂ x (H x)).re at h1
  change ‖countableContinuousNoiseTwo μ p hp β hβ hb (spanningSets μ) hcov hloc
    M hM hMc (N+2) x‖^2 ≤ β*‖1-M^2‖^2*(inner ℂ x (H x)).re at h2
  change (γ-C*‖1-M^2‖-β*‖1-M^2‖^2)*(inner ℂ x (H x)).re ≤ ‖H x‖^2
  nlinarith only [hg,h1,h2]

include hMc hcov hloc hU0 hU1 hpw hω hωm hC hrowInt hrow in
theorem countable_continuous_transfer_norm (γ : ℝ) (N : ℕ)
    (hgap : ∀ k ≤ N,
      (countablePairLift k (countableContinuousPairOperator μ p hp β hβ hb) *
        countablePairLift k (countableContinuousPairOperator μ p hp β hβ hb) -
        (γ : ℂ) • countablePairLift k (countableContinuousPairOperator μ p hp β hβ hb)).IsPositive)
    (x : countableSector N) :
    (γ-C*‖1-M^2‖-β*‖1-M^2‖^2) *
      (inner ℂ x (countableContinuousFilteredHamiltonian μ p hp β hβ hb M hM N x)).re ≤
      ‖countableContinuousFilteredHamiltonian μ p hp β hβ hb M hM N x‖^2 := by
  rcases N with _ | N
  · simp [countableContinuousFilteredHamiltonian, countablePairLift_zero_sector]
  rcases N with _ | N
  · simp [countableContinuousFilteredHamiltonian, countablePairLift_one_sector]
  exact countable_continuous_transfer_norm_add_two μ p hp β hβ hb hcov hloc M hM hMc
    U hU0 hU1 hpw ω hω hωm C hC hrowInt hrow γ N hgap x

include hMc hcov hloc hU0 hU1 hpw hω hωm hC hrowInt hrow in
/-- All-vector operator inequality on each complete fixed-N Hilbert space. -/
theorem countable_continuous_transfer (γ : ℝ) (N : ℕ)
    (hgap : ∀ k ≤ N,
      (countablePairLift k (countableContinuousPairOperator μ p hp β hβ hb) *
        countablePairLift k (countableContinuousPairOperator μ p hp β hβ hb) -
        (γ : ℂ) • countablePairLift k (countableContinuousPairOperator μ p hp β hβ hb)).IsPositive) :
    let H := countableContinuousFilteredHamiltonian μ p hp β hβ hb M hM N
    (H*H - ((γ-C*‖1-M^2‖-β*‖1-M^2‖^2 : ℝ) : ℂ) • H).IsPositive := by
  dsimp only
  apply (quadratic_positive_norm_iff _
    (countableContinuousFilteredHamiltonian_positive μ p hp β hβ hb M hM hMc N) _).mpr
  intro x
  exact countable_continuous_transfer_norm μ p hp β hβ hb hcov hloc M hM hMc
    U hU0 hU1 hpw ω hω hωm C hC hrowInt hrow γ N hgap x

end VortexGap.Fermion
