import VortexGap.Transfer.CountableContinuousRaw
import VortexGap.Fermion.CountableHilbertFock
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory VortexGap.Frame
open scoped InnerProduct ENNReal ComplexOrder

/-- Native one-particle Hilbert data, implemented in proven unitary Fock coordinates.
The reference pair operator and sector gap are explicitly expressed in those coordinates.
No environment identity, noise estimate, or enlarged reference gap is an input. -/
theorem hilbert_continuous_frame_transfer
    {H α : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ]
    (e : H ≃ₗᵢ[ℂ] CountableOrbital) (U : α → (TwoSpace →ₗᵢ[ℂ] H))
    (hU0 : AEStronglyMeasurable (fun a => U a (PiLp.single 2 0 1)) μ)
    (hU1 : AEStronglyMeasurable (fun a => U a (PiLp.single 2 1 1)) μ)
    (hp : ∀ q, MemLp (fun a => inner ℂ
      (countableTwoFramePair (e.toLinearIsometry.comp (U a))) q) 2 μ)
    (β : ℝ) (hβ : 0 ≤ β)
    (hb : ∀ q, (∫ a, ‖inner ℂ (countableTwoFramePair
      (e.toLinearIsometry.comp (U a))) q‖^2 ∂μ) ≤ β * ‖q‖^2)
    (M : H →L[ℂ] H) (hM : 0 ≤ M) (hMc : ‖M‖ ≤ 1)
    (ω : α → ℝ) (hω : ∀ a, 0 < ω a) (hωm : AEStronglyMeasurable ω μ) (C : ℝ)
    (hrowInt : ∀ᵐ a ∂μ, Integrable (fun b => traceNormTwo
      ((U a).toContinuousLinearMap.adjoint.comp (U b).toContinuousLinearMap).toLinearMap * ω b) μ)
    (hrow : ∀ᵐ a ∂μ, (∫ b, traceNormTwo
      ((U a).toContinuousLinearMap.adjoint.comp (U b).toContinuousLinearMap).toLinearMap * ω b ∂μ)
        ≤ C * ω a)
    (γ : ℝ) (N : ℕ)
    (hgap : ∀ k ≤ N,
      let Q := countableContinuousPairOperator μ
        (fun a => countableTwoFramePair (e.toLinearIsometry.comp (U a))) hp β hβ hb
      (countablePairLift k Q * countablePairLift k Q - (γ : ℂ) • countablePairLift k Q).IsPositive) :
    let Hf := countableContinuousFilteredHamiltonian μ
      (fun a => countableTwoFramePair (e.toLinearIsometry.comp (U a))) hp β hβ hb
      (e.conjStarAlgEquiv M) (hilbertCoordinates_filter_nonneg e M hM) N
    (Hf*Hf - ((γ-C*‖1-M^2‖-β*‖1-M^2‖^2 : ℝ) : ℂ) • Hf).IsPositive := by
  have hc : ‖e.conjStarAlgEquiv M‖ ≤ 1 := by
    rw [hilbertCoordinates_filter_norm]
    exact hMc
  have h := countable_continuous_frame_transfer μ
    (fun a => e.toLinearIsometry.comp (U a))
    (e.continuous.comp_aestronglyMeasurable hU0)
    (e.continuous.comp_aestronglyMeasurable hU1) hp β hβ hb
    (e.conjStarAlgEquiv M) (hilbertCoordinates_filter_nonneg e M hM) hc
    ω hω hωm C
    (by simpa only [hilbertCoordinates_overlap] using hrowInt)
    (by simpa only [hilbertCoordinates_overlap] using hrow) γ N hgap
  simpa only [hilbertCoordinates_filter_delta] using h
end VortexGap.Fermion