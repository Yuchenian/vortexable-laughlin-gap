import VortexGap.Fermion.ContinuousLossMoments
import VortexGap.Frame.ContinuousOneNoiseBound
import VortexGap.Frame.ContinuousTwoNoiseBound

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory VortexGap.Frame
open scoped InnerProduct ENNReal ComplexOrder

/-- Concrete continuous-frame CAR loss transfer on arbitrary finite-mode Fock space.
The environment decomposition, moments, both noises and enlarged reference gap are derived.
This controlled-label-measure theorem is not the infinite-mode extension. -/
theorem continuous_frame_transfer {n N : ℕ} {α : Type*} [MeasurableSpace α]
    (M : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1)
    (μ : Measure α) [IsFiniteMeasure μ] (U : α → TwoFrame n)
    (hU0 : AEStronglyMeasurable (fun a => U a (PiLp.single 2 0 1)) μ)
    (hU1 : AEStronglyMeasurable (fun a => U a (PiLp.single 2 1 1)) μ)
    (ω : α → ℝ) (hω : ∀ a, 0 < ω a) (hωm : AEStronglyMeasurable ω μ)
    (C : ℝ)
    (hrowInt : ∀ᵐ a ∂μ, Integrable (fun b => traceNormTwo (twoFrameOverlap (U a) (U b)) * ω b) μ)
    (hrow : ∀ᵐ a ∂μ, (∫ b, traceNormTwo (twoFrameOverlap (U a) (U b)) * ω b ∂μ) ≤ C * ω a)
    (β : ℝ) (hβ : 0 ≤ β)
    (hQ : ∀ q : PairSpace n, (inner ℂ q
      (continuousPairOperator μ (fun a => wedgePair (U a (PiLp.single 2 0 1))
        (U a (PiLp.single 2 1 1))) q)).re ≤ β * ‖q‖^2)
    (γ : ℝ)
    (hgap : ∀ K ≤ N, ∀ y : Space n, InSector K y →
      γ * (inner ℂ y (continuousFrameHamiltonian μ
        (fun a => wedgePair (U a (PiLp.single 2 0 1)) (U a (PiLp.single 2 1 1))) y)).re ≤
      (inner ℂ y ((continuousFrameHamiltonian μ
        (fun a => wedgePair (U a (PiLp.single 2 0 1)) (U a (PiLp.single 2 1 1))) *
        continuousFrameHamiltonian μ
        (fun a => wedgePair (U a (PiLp.single 2 0 1)) (U a (PiLp.single 2 1 1)))) y)).re)
    {x : Space n} (hx : InSector N x) :
    (γ - C * ‖1 - M^2‖ - β * ‖1 - M^2‖^2) *
      (inner ℂ x (continuousFrameHamiltonian μ (fun a => exteriorSquare M.toLinearMap
        (wedgePair (U a (PiLp.single 2 0 1)) (U a (PiLp.single 2 1 1)))) x)).re ≤
      (inner ℂ x ((continuousFrameHamiltonian μ (fun a => exteriorSquare M.toLinearMap
        (wedgePair (U a (PiLp.single 2 0 1)) (U a (PiLp.single 2 1 1)))) *
        continuousFrameHamiltonian μ (fun a => exteriorSquare M.toLinearMap
        (wedgePair (U a (PiLp.single 2 0 1)) (U a (PiLp.single 2 1 1))))) x)).re := by
  have hun := fun a => (twoFrameColumn_norm (U a) 0).le
  have hvn := fun a => (twoFrameColumn_norm (U a) 1).le
  have hp := wedgePair_memLp μ _ _ hU0 hU1 hun hvn
  have href := continuous_loss_compressed_reference_inequality M hM hc μ _ _ hU0 hU1 hun hvn γ hgap hx
  have h1 := continuousOneLossNoise_relative_form M μ hM hc U hU0 hU1 ω hω hωm C hrowInt hrow x
  have h2 := continuousTwoLossNoise_relative_form M μ _ hp β hβ hQ hM hc x
  simp only [add_apply, inner_add_right, Complex.add_re] at href
  nlinarith only [href, h1, h2]

end VortexGap.Fermion

