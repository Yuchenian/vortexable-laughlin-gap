import VortexGap.Frame.ContinuousPairLift

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory
open scoped InnerProduct ENNReal

variable {α : Type*} [MeasurableSpace α] {n m : ℕ}
  (μ : Measure α) (p : α → PairSpace n) (hp : MemLp p 2 μ)

include hp in
/-- Any concrete finite-mode orbital map preserves the controlled pair-field domain. -/
theorem exteriorPair_memLp
    (L : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m)) :
    MemLp (fun a => exteriorSquare L (p a)) 2 μ :=
  (LinearMap.toContinuousLinearMap (exteriorSquare L)).comp_memLp' hp

theorem pairGram_apply (q : PairSpace n) (x : Space n) :
    ((LinearMap.toContinuousLinearMap (pairAnnihilate q)).adjoint.comp
      (LinearMap.toContinuousLinearMap (pairAnnihilate q))) x =
      pairCreate q (pairAnnihilate q x) := by
  change (pairAnnihilate q).adjoint (pairAnnihilate q x) = _
  rw [pairAnnihilate_adjoint]

include hp in
theorem continuousFrameAction_integrable (x : Space n) :
    Integrable (fun a => pairCreate (p a) (pairAnnihilate (p a) x)) μ := by
  have h := (ContinuousLinearMap.apply ℂ (Space n) x).integrable_comp
    (continuousFrame_integrable μ p hp)
  simpa only [ContinuousLinearMap.apply_apply, pairGram_apply] using h

include hp in
/-- The actual Hamiltonian acts by the integral of the concrete CAR pair interaction. -/
theorem continuousFrameHamiltonian_apply (x : Space n) :
    continuousFrameHamiltonian μ p x = ∫ a, pairCreate (p a) (pairAnnihilate (p a) x) ∂μ := by
  rw [continuousFrameHamiltonian, ContinuousLinearMap.integral_apply (continuousFrame_integrable μ p hp)]
  simp only [pairGram_apply]

include hp in
theorem continuousFrameHamiltonian_adjoint :
    (continuousFrameHamiltonian μ p).adjoint = continuousFrameHamiltonian μ p := by
  rw [← continuousFrameAnalysis_gram μ p hp, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint]

end VortexGap.Fermion

