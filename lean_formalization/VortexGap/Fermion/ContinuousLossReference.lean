import VortexGap.Fermion.ContinuousLossOutput

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory
open scoped InnerProduct ENNReal ComplexOrder

variable {n : ℕ}
  (M : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
  (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1)

/-- The concrete unitary reference coordinates intertwine each actual pair interaction. -/
theorem lossReferenceCoordinates_pairInteraction (q : PairSpace n) (x : Space (n+n)) :
    lossReferenceCoordinates M hM hc
      (pairCreate (exteriorSquare (finiteLossEmbedding M hM hc).toLinearMap q)
        (pairAnnihilate (exteriorSquare (finiteLossEmbedding M hM hc).toLinearMap q) x)) =
      referenceAmplify (pairLift (pairRankOne q)) (lossReferenceCoordinates M hM hc x) := by
  have h := lossReferenceCoordinates_hamiltonian M hM hc (fun _ : Unit => 1) (fun _ => q) x
  simpa only [lossHamiltonian, frameHamiltonian, Fintype.sum_unique, Complex.ofReal_one,
    one_smul, pairLift_rankOne, pairAnnihilate_adjoint, Module.End.mul_apply] using h

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)
  (p : α → PairSpace n) (hp : MemLp p 2 μ)

include hp in
/-- Actual continuous H0(J) is the original H0 with spectator identity, in derived unitary coordinates. -/
theorem continuousLossReference_coordinates (x : Space (n+n)) :
    lossReferenceCoordinates M hM hc (continuousLossHamiltonian M hM hc μ p x) =
      referenceAmplify (continuousFrameHamiltonian μ p).toLinearMap
        (lossReferenceCoordinates M hM hc x) := by
  haveI : CompleteSpace (Space (n+n)) := PiLp.completeSpace 2 (fun _ => ℂ)
  haveI : CompleteSpace (Space n) := PiLp.completeSpace 2 (fun _ => ℂ)
  haveI : CompleteSpace (SplitSpace n n) := PiLp.completeSpace 2 (fun _ => ℂ)
  haveI : CompleteSpace (Space n →L[ℂ] Space n) := ContinuousLinearMap.instCompleteSpace
  let y := lossReferenceCoordinates M hM hc x
  let L : (Space n →L[ℂ] Space n) →L[ℂ] SplitSpace n n :=
    ({ toFun := fun H => referenceAmplify H.toLinearMap y
       map_add' H K := by ext AB; rfl
       map_smul' z H := by ext AB; rfl } :
      (Space n →L[ℂ] Space n) →ₗ[ℂ] SplitSpace n n).toContinuousLinearMap
  have hcoords (f : α → Space (n+n)) :
      lossReferenceCoordinates M hM hc (∫ a, f a ∂μ) =
        ∫ a, lossReferenceCoordinates M hM hc (f a) ∂μ :=
    ((lossReferenceCoordinates M hM hc).toLinearIsometry.integral_comp_comm f).symm
  rw [continuousLossHamiltonian, continuousFrameHamiltonian_apply μ _
    (exteriorPair_memLp μ p hp (finiteLossEmbedding M hM hc).toLinearMap), hcoords]
  simp_rw [lossReferenceCoordinates_pairInteraction]
  have hpair (a : α) : referenceAmplify (pairLift (pairRankOne (p a))) y =
      L ((LinearMap.toContinuousLinearMap (pairAnnihilate (p a))).adjoint.comp
        (LinearMap.toContinuousLinearMap (pairAnnihilate (p a)))) := by
    change referenceAmplify (pairLift (pairRankOne (p a))) y =
      referenceAmplify ((pairAnnihilate (p a)).adjoint.comp (pairAnnihilate (p a))) y
    rw [pairLift_rankOne]
    rfl
  change (∫ a, referenceAmplify (pairLift (pairRankOne (p a))) y ∂μ) =
    L (continuousFrameHamiltonian μ p)
  simp_rw [hpair]
  exact L.integral_comp_comm (continuousFrame_integrable μ p hp)

include hp in
/-- Enlarged gap derived from the original reference sectors; no cutoff gap is used. -/
theorem continuousLossHamiltonian_sector_inequality {N : ℕ} (γ : ℝ)
    (hgap : ∀ K ≤ N, ∀ z : Space n, InSector K z →
      γ * (inner ℂ z (continuousFrameHamiltonian μ p z)).re ≤
        (inner ℂ z ((continuousFrameHamiltonian μ p * continuousFrameHamiltonian μ p) z)).re)
    {x : Space (n+n)} (hx : InSector N x) :
    γ * (inner ℂ x (continuousLossHamiltonian M hM hc μ p x)).re ≤
      (inner ℂ x ((continuousLossHamiltonian M hM hc μ p *
        continuousLossHamiltonian M hM hc μ p) x)).re := by
  have h := referenceAmplify_sector_inequality (continuousFrameHamiltonian μ p).toLinearMap γ hgap
    (finiteLossFock_sector M hM hc hx)
  change γ * (inner ℂ (lossReferenceCoordinates M hM hc x)
      (referenceAmplify (continuousFrameHamiltonian μ p).toLinearMap
        (lossReferenceCoordinates M hM hc x))).re ≤
    (inner ℂ (lossReferenceCoordinates M hM hc x)
      (referenceAmplify (continuousFrameHamiltonian μ p).toLinearMap
        (referenceAmplify (continuousFrameHamiltonian μ p).toLinearMap
          (lossReferenceCoordinates M hM hc x)))).re at h
  rw [← continuousLossReference_coordinates M hM hc μ p hp,
    ← continuousLossReference_coordinates M hM hc μ p hp] at h
  simpa only [(lossReferenceCoordinates M hM hc).inner_map_map, mul_apply_eq_comp] using h

end VortexGap.Fermion

