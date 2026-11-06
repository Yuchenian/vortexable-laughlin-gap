import VortexGap.Transfer.CountableContinuousFrame
import VortexGap.Frame.CountablePairFrameFields
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory Filter VortexGap.Frame
open scoped InnerProduct ENNReal ComplexOrder

theorem countableSchurConstant_nonneg
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (hμ : μ ≠ 0)
    (U : α → CountableTwoFrame) (ω : α → ℝ) (hω : ∀ a, 0 < ω a) (C : ℝ)
    (hrow : ∀ᵐ a ∂μ,
      (∫ b, traceNormTwo (countableTwoFrameOverlap (U a) (U b)) * ω b ∂μ) ≤ C * ω a) :
    0 ≤ C := by
  haveI : (ae μ).NeBot := ae_neBot.mpr hμ
  obtain ⟨a, ha⟩ := hrow.exists
  have hi : 0 ≤ ∫ b, traceNormTwo (countableTwoFrameOverlap (U a) (U b)) * ω b ∂μ :=
    integral_nonneg fun b => mul_nonneg (traceNormTwo_nonneg _) (hω b).le
  have hc := hi.trans ha
  by_contra hn
  have hneg := mul_neg_of_neg_of_pos (lt_of_not_ge hn) (hω a)
  linarith

theorem countableContinuousPairOperator_zero_measure
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (p : α → CountablePairSpace)
    (hp : ∀ q, MemLp (fun a => inner ℂ (p a) q) 2 μ)
    (β : ℝ) (hβ : 0 ≤ β)
    (hb : ∀ q, (∫ a, ‖inner ℂ (p a) q‖^2 ∂μ) ≤ β * ‖q‖^2) (hμ : μ = 0) :
    countableContinuousPairOperator μ p hp β hβ hb = 0 := by
  subst μ
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  rw [countableContinuousPairOperator_inner]
  simp

theorem countableContinuousFilteredHamiltonian_zero_measure
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (p : α → CountablePairSpace)
    (hp : ∀ q, MemLp (fun a => inner ℂ (p a) q) 2 μ)
    (β : ℝ) (hβ : 0 ≤ β)
    (hb : ∀ q, (∫ a, ‖inner ℂ (p a) q‖^2 ∂μ) ≤ β * ‖q‖^2) (hμ : μ = 0)
    (M : CountableOrbital →L[ℂ] CountableOrbital) (hM : 0 ≤ M) (N : ℕ) :
    countableContinuousFilteredHamiltonian μ p hp β hβ hb M hM N = 0 := by
  simp only [countableContinuousFilteredHamiltonian,
    countableContinuousPairOperator_zero_measure μ p hp β hβ hb hμ,
    ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero, countablePairLift_zero]

/-- Raw measurable two-frame entrance: no local integrability, cover, noise, or enlarged-gap premise.
The Schur constant is an arbitrary real number; its sign is derived or the zero measure is handled. -/
theorem countable_continuous_frame_transfer
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
    (H*H - ((γ-C*‖1-M^2‖-β*‖1-M^2‖^2 : ℝ) : ℂ) • H).IsPositive := by
  dsimp only
  by_cases hμ : μ = 0
  · rw [countableContinuousFilteredHamiltonian_zero_measure μ _ hp β hβ hb hμ M hM N]
    have hz : (0 : countableSector N →L[ℂ] countableSector N) * 0 -
        ((γ-C*‖1-M^2‖-β*‖1-M^2‖^2 : ℝ) : ℂ) • 0 = 0 := by
      ext x; simp
    rw [hz]
    exact ContinuousLinearMap.isPositive_zero
  · exact countable_continuous_transfer μ _ hp β hβ hb
      (increasingCutoffs_aecover μ (spanningSets μ) (measurableSet_spanningSets μ)
        (monotone_spanningSets μ) (iUnion_spanningSets μ))
      (countableTwoFramePair_spanning_memLp μ U hU0 hU1) M hM hMc U hU0 hU1
      (fun _ => rfl) ω hω hωm C (countableSchurConstant_nonneg μ hμ U ω hω C hrow)
      hrowInt hrow γ N hgap

end VortexGap.Fermion
