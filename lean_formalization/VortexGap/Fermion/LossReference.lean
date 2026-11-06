import VortexGap.Fermion.ReferencePair

/-! Concrete loss Hamiltonian and reference-sector inequality via the derived Fock unitary. -/
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped BigOperators InnerProduct ComplexOrder

/-- The actual weighted pair lift, with no spectral hypothesis in its definition. -/
def frameHamiltonian {n : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (p : ι → PairSpace n) : Module.End ℂ (Space n) :=
  pairLift (∑ i, (w i : ℂ) • pairRankOne (p i))

/-- The same reference pair interaction embedded in the first block of orbitals. -/
def embeddedReferenceHamiltonian {n : ℕ} (m : ℕ) {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (p : ι → PairSpace n) : Module.End ℂ (Space (n+m)) :=
  frameHamiltonian w (fun i => exteriorSquare (orbitalEnv n m).toLinearMap (p i))

/-- H0(b), formed from Jv=(Ev,Mv) and the original pair frame. -/
def lossHamiltonian {n : ℕ} (M : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1) {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (p : ι → PairSpace n) : Module.End ℂ (Space (n+n)) :=
  frameHamiltonian w (fun i => exteriorSquare (finiteLossEmbedding M hM hc).toLinearMap (p i))

theorem finiteLossRotation_pair_env {n : ℕ}
    (M : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1)
    (p : PairSpace n) :
    exteriorSquare (finiteLossRotation M hM hc).toLinearEquiv.toLinearMap
        (exteriorSquare (orbitalEnv n n).toLinearMap p) =
      exteriorSquare (finiteLossEmbedding M hM hc).toLinearMap p := by
  have he : (finiteLossRotation M hM hc).toLinearEquiv.toLinearMap.comp
      (orbitalEnv n n).toLinearMap = (finiteLossEmbedding M hM hc).toLinearMap := by
    apply LinearMap.ext
    exact finiteLossRotation_env M hM hc
  rw [← LinearMap.comp_apply, ← exteriorSquare_comp, he]

theorem finiteLossFock_frame {n : ℕ}
    (M : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1)
    {ι : Type*} [Fintype ι] (w : ι → ℝ) (p : ι → PairSpace n) (x : Space (n+n)) :
    lossHamiltonian M hM hc w p (finiteLossFock M hM hc x) =
      finiteLossFock M hM hc (embeddedReferenceHamiltonian n w p x) := by
  have h := congrArg (fun T => T x)
    (fockMap_frameInteraction (finiteLossRotation M hM hc).toLinearIsometry w
      (fun i => exteriorSquare (orbitalEnv n n).toLinearMap (p i)))
  change frameHamiltonian w (fun i =>
      exteriorSquare (finiteLossRotation M hM hc).toLinearEquiv.toLinearMap
        (exteriorSquare (orbitalEnv n n).toLinearMap (p i))) (finiteLossFock M hM hc x) =
      finiteLossFock M hM hc (embeddedReferenceHamiltonian n w p x) at h
  simp_rw [finiteLossRotation_pair_env] at h
  exact h

theorem finiteLossFock_frame_reverse {n : ℕ}
    (M : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1)
    {ι : Type*} [Fintype ι] (w : ι → ℝ) (p : ι → PairSpace n) (x : Space (n+n)) :
    finiteLossFock M hM hc (lossHamiltonian M hM hc w p x) =
      embeddedReferenceHamiltonian n w p (finiteLossFock M hM hc x) := by
  have h := finiteLossFock_frame M hM hc w p (finiteLossFock M hM hc x)
  rw [finiteLossFock_involutive] at h
  have h' := congrArg (finiteLossFock M hM hc) h
  rw [finiteLossFock_involutive] at h'
  exact h'

/-- Actual unitary coordinates in which the reference subsystem is the first factor. -/
def lossReferenceCoordinates {n : ℕ}
    (M : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1) :
    Space (n+n) ≃ₗᵢ[ℂ] SplitSpace n n :=
  (finiteLossFock M hM hc).trans (fockSplit n n)

theorem lossReferenceCoordinates_hamiltonian {n : ℕ}
    (M : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1)
    {ι : Type*} [Fintype ι] (w : ι → ℝ) (p : ι → PairSpace n) (x : Space (n+n)) :
    lossReferenceCoordinates M hM hc (lossHamiltonian M hM hc w p x) =
      referenceAmplify (frameHamiltonian w p) (lossReferenceCoordinates M hM hc x) := by
  change fockSplit n n (finiteLossFock M hM hc (lossHamiltonian M hM hc w p x)) = _
  rw [finiteLossFock_frame_reverse]
  exact fockSplit_frameInteraction_env w p _

/-- The enlarged reference inequality is proved from actual reference sectors 0..N.
No amplified gap, environment formula or relative-noise estimate is a hypothesis. -/
theorem lossHamiltonian_sector_inequality {n N : ℕ}
    (M : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1)
    {ι : Type*} [Fintype ι] (w : ι → ℝ) (p : ι → PairSpace n) (γ : ℝ)
    (hgap : ∀ K ≤ N, ∀ y : Space n, InSector K y →
      γ * (inner ℂ y (frameHamiltonian w p y)).re ≤
        (inner ℂ y ((frameHamiltonian w p * frameHamiltonian w p) y)).re)
    {x : Space (n+n)} (hx : InSector N x) :
    γ * (inner ℂ x (lossHamiltonian M hM hc w p x)).re ≤
      (inner ℂ x ((lossHamiltonian M hM hc w p * lossHamiltonian M hM hc w p) x)).re := by
  have h := referenceAmplify_sector_inequality (frameHamiltonian w p) γ hgap
    (finiteLossFock_sector M hM hc hx)
  change γ * (inner ℂ (lossReferenceCoordinates M hM hc x)
      (referenceAmplify (frameHamiltonian w p) (lossReferenceCoordinates M hM hc x))).re ≤
    (inner ℂ (lossReferenceCoordinates M hM hc x)
      (referenceAmplify (frameHamiltonian w p)
        (referenceAmplify (frameHamiltonian w p) (lossReferenceCoordinates M hM hc x)))).re at h
  rw [← lossReferenceCoordinates_hamiltonian, ← lossReferenceCoordinates_hamiltonian] at h
  simpa only [(lossReferenceCoordinates M hM hc).inner_map_map, Module.End.mul_apply] using h

end VortexGap.Fermion
