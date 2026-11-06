import VortexGap.Frame.CountableFilteredPair

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory Filter
open scoped InnerProduct ENNReal ComplexOrder

theorem countablePairFilter_contract
    (M : CountableOrbital →L[ℂ] CountableOrbital) (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1) :
    ‖countablePairFilter M hM‖ ≤ 1 := by
  apply (countablePairFilter_norm_le M hM).trans
  nlinarith [norm_nonneg M]

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) (p : α → CountablePairSpace)
  (hp : ∀ q, MemLp (fun a => inner ℂ (p a) q) 2 μ)
  (β : ℝ) (hβ : 0 ≤ β)
  (hb : ∀ q, (∫ a, ‖inner ℂ (p a) q‖^2 ∂μ) ≤ β * ‖q‖^2)
  (s : ℕ → Set α) (hc : AECover μ atTop s)
  (hloc : ∀ n, MemLp p 2 (μ.restrict (s n)))
  (hm : Monotone s) (hu : ⋃ n, s n = Set.univ)

include hc hloc hm hu in
/-- Filtering the actual CAR field gives the lift of F Q F-adjoint on every fixed sector. -/
theorem countableFilteredFrame_energy
    (F : CountablePairSpace →L[ℂ] CountablePairSpace) (hF : ‖F‖ ≤ 1)
    (N : ℕ) (x : countableSector N) :
    (∫ a, ‖countablePairAnnihilate N (F (p a)) x‖^2 ∂μ) =
      (inner ℂ x (countablePairLift N
        (F.comp ((countableContinuousPairOperator μ p hp β hβ hb).comp F.adjoint)) x)).re := by
  rw [← countableFilteredPair_operator μ p hp β hβ hb F hF]
  exact (countableContinuousFrame_energy μ (fun a => F (p a))
    (countableFilteredPair_coeff_memLp μ p hp F) β hβ
    (countableFilteredPair_bessel μ p β hβ hb F hF) s hc
    (fun n => countableFilteredPair_local_memLp μ p F (s n) (hloc n)) hm hu N x).symm

include hc hloc hm hu in
/-- Specialization to the concrete exterior-square filter constructed from fermion loss. -/
theorem countableLossFilteredFrame_energy
    (M : CountableOrbital →L[ℂ] CountableOrbital) (hM : 0 ≤ M) (hMc : ‖M‖ ≤ 1)
    (N : ℕ) (x : countableSector N) :
    (∫ a, ‖countablePairAnnihilate N (countablePairFilter M hM (p a)) x‖^2 ∂μ) =
      (inner ℂ x (countablePairLift N
        ((countablePairFilter M hM).comp
          ((countableContinuousPairOperator μ p hp β hβ hb).comp
            (countablePairFilter M hM).adjoint)) x)).re :=
  countableFilteredFrame_energy μ p hp β hβ hb s hc hloc hm hu
    (countablePairFilter M hM) (countablePairFilter_contract M hM hMc) N x

end VortexGap.Fermion
