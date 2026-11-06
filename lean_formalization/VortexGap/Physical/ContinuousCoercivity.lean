import VortexGap.Physical.CoercivityGap
import VortexGap.Transfer.CountableContinuousRaw
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory Filter VortexGap.Frame
open scoped InnerProduct ENNReal ComplexOrder

/-- Raw continuous-frame weighted comparison. Only the original reference sectors
carry a gap hypothesis; the normalized filtered gap is proved by concrete loss. -/
theorem continuous_coercivity_kernel_gap
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ]
    (U : α → CountableTwoFrame)
    (hU0 : AEStronglyMeasurable (fun a => U a (PiLp.single 2 0 1)) μ)
    (hU1 : AEStronglyMeasurable (fun a => U a (PiLp.single 2 1 1)) μ)
    (hp : ∀ q, MemLp (fun a => inner ℂ (countableTwoFramePair (U a)) q) 2 μ)
    (β : ℝ) (hβ : 0 ≤ β)
    (hb : ∀ q, (∫ a, ‖inner ℂ (countableTwoFramePair (U a)) q‖^2 ∂μ) ≤ β * ‖q‖^2)
    (R : CountableOrbital →L[ℂ] CountableOrbital) (hR : 0 ≤ R)
    (g : ℝ) (hg : 0 < g) (hMc : ‖(Real.sqrt g : ℂ) • R‖ ≤ 1)
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
          (countableContinuousPairOperator μ (fun a => countableTwoFramePair (U a)) hp β hβ hb)).IsPositive)
    (W : CountablePairSpace →L[ℂ] CountablePairSpace)
    (κ K : ℝ) (hκ : 0 < κ)
    (hlo : (κ : ℂ) • countableContinuousPairOperator μ
      (fun a => countableTwoFramePair (U a)) hp β hβ hb ≤ W)
    (hhi : W ≤ (K : ℂ) • countableContinuousPairOperator μ
      (fun a => countableTwoFramePair (U a)) hp β hβ hb) :
    let M := (Real.sqrt g : ℂ) • R
    let hM : 0 ≤ M := smul_nonneg
      (show 0 ≤ (Real.sqrt g : ℂ) by exact_mod_cast Real.sqrt_nonneg g) hR
    let B := countableContinuousFilteredHamiltonian μ
      (fun a => countableTwoFramePair (U a)) hp β hβ hb M hM N
    let A := filteredPairHamiltonian N R hR W
    LinearMap.ker A.toLinearMap = LinearMap.ker B.toLinearMap ∧
      ∀ x ∈ (LinearMap.ker A.toLinearMap)ᗮ,
        (κ/g^2*(γ-C*‖1-M^2‖-β*‖1-M^2‖^2))*‖x‖^2 ≤
          (inner ℂ x (A x)).re := by
  dsimp only
  let M := (Real.sqrt g : ℂ) • R
  have hM : 0 ≤ M := smul_nonneg
    (show 0 ≤ (Real.sqrt g : ℂ) by exact_mod_cast Real.sqrt_nonneg g) hR
  have ht := countable_continuous_frame_transfer μ U hU0 hU1 hp β hβ hb
    M hM hMc ω hω hωm C hrowInt hrow γ N hgap
  have hQ := ContinuousLinearMap.nonneg_iff_isPositive.mpr
    (countableContinuousPairOperator_positive μ _ hp β hβ hb)
  have he := filteredPairHamiltonian_eq_continuous μ
    (fun a => countableTwoFramePair (U a)) hp β hβ hb M hM N
  have hh := filtered_coercivity_kernel_gap N R hR _ W hQ κ K g
    (γ-C*‖1-M^2‖-β*‖1-M^2‖^2) hκ hg hlo hhi
  dsimp only at hh
  rw [he] at hh
  exact hh ht

end VortexGap.Fermion
