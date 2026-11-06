import VortexGap.Frame.CountableFilteredPair
import VortexGap.Frame.CountableContinuousLift
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory Filter
open scoped InnerProduct ENNReal Topology
attribute [local instance] pairOperatorNormed sectorOperatorNormed
variable {α : Type*} [MeasurableSpace α] (μ : Measure α) (p : α → CountablePairSpace)

theorem countablePairLift_rankOne_apply_integrable
    (hloc : MemLp p 2 μ) (N : ℕ) (x : countableSector N) :
    Integrable (fun a => countablePairLift N (InnerProductSpace.rankOne ℂ (p a) (p a)) x) μ := by
  have h := (ContinuousLinearMap.apply ℂ (countableSector N) x).integrable_comp
    (countablePairHamiltonian_integrable μ p hloc N)
  convert h using 1
  funext a
  exact congrArg (fun T : countableSector N →L[ℂ] countableSector N => T x)
    (countablePairLift_rankOne N (p a) (p a))

theorem countablePairLift_rankOne_apply_integral
    (hloc : MemLp p 2 μ) (N : ℕ) (x : countableSector N) :
    (∫ a, countablePairLift N (InnerProductSpace.rankOne ℂ (p a) (p a)) x ∂μ) =
      countablePairLift N (∫ a, InnerProductSpace.rankOne ℂ (p a) (p a) ∂μ) x := by
  rw [countablePairLift_integral μ p hloc N]
  change _ = (ContinuousLinearMap.apply ℂ (countableSector N) x)
    (∫ a, (countablePairAnnihilate N (p a)).adjoint.comp (countablePairAnnihilate N (p a)) ∂μ)
  rw [← (ContinuousLinearMap.apply ℂ (countableSector N) x).integral_comp_comm
    (countablePairHamiltonian_integrable μ p hloc N)]
  apply integral_congr_ae
  exact Eventually.of_forall fun a =>
    congrArg (fun T : countableSector N →L[ℂ] countableSector N => T x)
      (countablePairLift_rankOne N (p a) (p a))

variable (hp : ∀ q, MemLp (fun a => inner ℂ (p a) q) 2 μ)
  (β : ℝ) (hβ : 0 ≤ β)
  (hb : ∀ q, (∫ a, ‖inner ℂ (p a) q‖^2 ∂μ) ≤ β * ‖q‖^2)
  (s : ℕ → Set α) (hc : AECover μ atTop s)
  (hloc : ∀ n, MemLp p 2 (μ.restrict (s n)))
  (hm : Monotone s) (hu : ⋃ n, s n = Set.univ)

include hc hloc hm hu in
theorem countableContinuousPairLift_integral_tendsto (N : ℕ) (x : countableSector N) :
    Tendsto (fun n => ∫ a in s n,
      countablePairLift N (InnerProductSpace.rankOne ℂ (p a) (p a)) x ∂μ) atTop
      (𝓝 (countablePairLift N (countableContinuousPairOperator μ p hp β hβ hb) x)) := by
  have he (n : ℕ) : (∫ a in s n,
      countablePairLift N (InnerProductSpace.rankOne ℂ (p a) (p a)) x ∂μ) =
      countablePairLift N (countableContinuousPairCutoff μ p hp β hβ hb (s n) (hc.measurableSet n)) x := by
    rw [countableContinuousPairCutoff_integral μ p hp β hβ hb (s n) (hc.measurableSet n) (hloc n)]
    exact countablePairLift_rankOne_apply_integral (μ.restrict (s n)) p (hloc n) N x
  have h := countableContinuousPairLift_tendsto μ p hp β hβ hb s hc.measurableSet hm hu N x
  simpa only [← he] using h

include hc hloc hm hu in
theorem countableFilteredPairLift_integral_tendsto
    (F : CountablePairSpace →L[ℂ] CountablePairSpace) (hF : ‖F‖ ≤ 1)
    (N : ℕ) (x : countableSector N) :
    Tendsto (fun n => ∫ a in s n,
      countablePairLift N (InnerProductSpace.rankOne ℂ (F (p a)) (F (p a))) x ∂μ) atTop
      (𝓝 (countablePairLift N
        (F.comp ((countableContinuousPairOperator μ p hp β hβ hb).comp F.adjoint)) x)) := by
  have h := countableContinuousPairLift_integral_tendsto μ (fun a => F (p a))
    (countableFilteredPair_coeff_memLp μ p hp F) β hβ
    (countableFilteredPair_bessel μ p β hβ hb F hF) s hc
    (fun n => countableFilteredPair_local_memLp μ p F (s n) (hloc n)) hm hu N x
  rw [countableFilteredPair_operator μ p hp β hβ hb F hF] at h
  exact h

include hc hloc hm hu in
/-- Fixed-sector Hamiltonian integrals also converge after an actual bounded output map. -/
theorem countableFilteredPairLift_output_integral_tendsto
    (F : CountablePairSpace →L[ℂ] CountablePairSpace) (hF : ‖F‖ ≤ 1)
    (N : ℕ) (x : countableSector N) (T : countableSector N →L[ℂ] CountableSpace) :
    Tendsto (fun n => ∫ a in s n,
      T (countablePairLift N (InnerProductSpace.rankOne ℂ (F (p a)) (F (p a))) x) ∂μ) atTop
      (𝓝 (T (countablePairLift N
        (F.comp ((countableContinuousPairOperator μ p hp β hβ hb).comp F.adjoint)) x))) := by
  have h := (T.continuous.tendsto _).comp
    (countableFilteredPairLift_integral_tendsto μ p hp β hβ hb s hc hloc hm hu F hF N x)
  have he (n : ℕ) := T.integral_comp_comm
    (countablePairLift_rankOne_apply_integrable (μ.restrict (s n)) (fun a => F (p a))
      (countableFilteredPair_local_memLp μ p F (s n) (hloc n)) N x)
  simpa only [Function.comp_def, ← he] using h

end VortexGap.Fermion
