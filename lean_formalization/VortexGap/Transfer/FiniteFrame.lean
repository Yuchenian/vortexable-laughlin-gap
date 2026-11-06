import VortexGap.Frame.OneNoiseBound
import VortexGap.Frame.TwoNoiseBound

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open VortexGap.Frame
open scoped BigOperators InnerProduct ComplexOrder

/-- Concrete finite-dimensional fermionic loss transfer. All environment identities
and noise bounds are derived from CAR; only raw frame and reference-sector data enter. -/
theorem finite_frame_transfer {n N : ℕ} {ι : Type*} [Fintype ι]
    (M : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (U : ι → TwoFrame n)
    (ω : ι → ℝ) (hω : ∀ i, 0 < ω i) (C : ℝ)
    (hrow : ∀ i, ∑ j, w j * traceNormTwo (twoFrameOverlap (U i) (U j)) * ω j ≤ C * ω i)
    (β : ℝ) (hβ : 0 ≤ β)
    (hQ : ∀ q : PairSpace n,
      (inner ℂ q ((∑ i, (w i : ℂ) • pairRankOne
        (wedgePair (U i (PiLp.single 2 0 1)) (U i (PiLp.single 2 1 1)))) q)).re ≤ β * ‖q‖^2)
    (γ : ℝ)
    (hgap : ∀ K ≤ N, ∀ y : Space n, InSector K y →
      γ * (inner ℂ y (frameHamiltonian w
        (fun i => wedgePair (U i (PiLp.single 2 0 1)) (U i (PiLp.single 2 1 1))) y)).re ≤
      (inner ℂ y ((frameHamiltonian w
        (fun i => wedgePair (U i (PiLp.single 2 0 1)) (U i (PiLp.single 2 1 1))) *
        frameHamiltonian w
        (fun i => wedgePair (U i (PiLp.single 2 0 1)) (U i (PiLp.single 2 1 1)))) y)).re)
    {x : Space n} (hx : InSector N x) :
    (γ - C * ‖1 - M^2‖ - β * ‖1 - M^2‖^2) *
      (inner ℂ x (filteredHamiltonian M w
        (fun i => wedgePair (U i (PiLp.single 2 0 1)) (U i (PiLp.single 2 1 1))) x)).re ≤
      (inner ℂ x ((filteredHamiltonian M w
        (fun i => wedgePair (U i (PiLp.single 2 0 1)) (U i (PiLp.single 2 1 1))) *
        filteredHamiltonian M w
        (fun i => wedgePair (U i (PiLp.single 2 0 1)) (U i (PiLp.single 2 1 1)))) x)).re := by
  have href := loss_compressed_reference_inequality M hM hc w
    (fun i => U i (PiLp.single 2 0 1)) (fun i => U i (PiLp.single 2 1 1)) γ hgap hx
  have h1 := oneLossNoise_relative_form M hM hc w hw U ω hω C hrow x
  have h2 := twoLossNoise_relative_form M hM hc w hw
    (fun i => wedgePair (U i (PiLp.single 2 0 1)) (U i (PiLp.single 2 1 1))) β hβ hQ x
  simp only [LinearMap.add_apply, inner_add_right, Complex.add_re] at href
  nlinarith only [href, h1, h2]

end VortexGap.Fermion
