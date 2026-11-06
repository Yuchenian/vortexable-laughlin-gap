import VortexGap.Transfer.CountableContinuousRaw
import VortexGap.Operator.SpectralGap
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory VortexGap.Frame
open scoped InnerProduct ENNReal ComplexOrder
theorem countable_continuous_frame_spectrum_gap
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ]
    (U : α → CountableTwoFrame)
    (hU0 : AEStronglyMeasurable (fun a => U a (PiLp.single 2 0 1)) μ)
    (hU1 : AEStronglyMeasurable (fun a => U a (PiLp.single 2 1 1)) μ)
    (hp : ∀ q, MemLp (fun a => inner ℂ (countableTwoFramePair (U a)) q) 2 μ)
    (β : ℝ) (hβ : 0 ≤ β)
    (hb : ∀ q, (∫ a, ‖inner ℂ (countableTwoFramePair (U a)) q‖^2 ∂μ) ≤ β * ‖q‖^2)
    (M : CountableOrbital →L[ℂ] CountableOrbital) (hM : 0 ≤ M) (hMc : ‖M‖ ≤ 1)
    (ω : α → ℝ) (hω : ∀ a, 0 < ω a) (hωm : AEStronglyMeasurable ω μ) (C : ℝ)
    (hrowInt : ∀ᵐ a ∂μ, Integrable
      (fun b => traceNormTwo (countableTwoFrameOverlap (U a) (U b)) * ω b) μ)
    (hrow : ∀ᵐ a ∂μ,
      (∫ b, traceNormTwo (countableTwoFrameOverlap (U a) (U b)) * ω b ∂μ) ≤ C * ω a)
    (γ : ℝ) (N : ℕ)
    (hgap : ∀ k ≤ N,
      (countablePairLift k (countableContinuousPairOperator μ (fun a => countableTwoFramePair (U a)) hp β hβ hb) *
        countablePairLift k (countableContinuousPairOperator μ (fun a => countableTwoFramePair (U a)) hp β hβ hb) -
        (γ : ℂ) • countablePairLift k
          (countableContinuousPairOperator μ (fun a => countableTwoFramePair (U a)) hp β hβ hb)).IsPositive) :
    let H := countableContinuousFilteredHamiltonian μ (fun a => countableTwoFramePair (U a)) hp β hβ hb M hM N
    Disjoint (spectrum ℝ H) (Set.Ioo 0 (γ-C*‖1-M^2‖-β*‖1-M^2‖^2)) := by
  dsimp only
  exact VortexGap.quadratic_gap_spectrum_excludes _
    (countableContinuousFilteredHamiltonian_positive μ _ hp β hβ hb M hM hMc N) _
    (countable_continuous_frame_transfer μ U hU0 hU1 hp β hβ hb M hM hMc
      ω hω hωm C hrowInt hrow γ N hgap)
end VortexGap.Fermion