import VortexGap.Frame.CountableFilteredPair
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory Filter
open scoped ComplexOrder
variable {α : Type*} [MeasurableSpace α] (μ : Measure α) (p : α → CountablePairSpace)
  (hp : ∀ q, MemLp (fun a => inner ℂ (p a) q) 2 μ)
  (β : ℝ) (hβ : 0 ≤ β)
  (hb : ∀ q, (∫ a, ‖inner ℂ (p a) q‖^2 ∂μ) ≤ β*‖q‖^2)
  (D : CountablePairSpace →L[ℂ] CountablePairSpace)

include hβ hb in
theorem countableBoundedFilter_bessel (q : CountablePairSpace) :
    (∫ a, ‖inner ℂ (D (p a)) q‖^2 ∂μ) ≤ (β*‖D‖^2)*‖q‖^2 := by
  simp_rw [← ContinuousLinearMap.adjoint_inner_right]
  have hn := D.adjoint.le_opNorm q
  rw [ContinuousLinearMap.adjoint.norm_map] at hn
  calc
    _ ≤ β*‖D.adjoint q‖^2 := hb _
    _ ≤ β*(‖D‖*‖q‖)^2 := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) hn 2) hβ
    _ = _ := by ring

theorem countableBoundedFilter_analysis :
    countableContinuousPairAnalysis μ (fun a => D (p a))
      (countableFilteredPair_coeff_memLp μ p hp D) (β*‖D‖^2)
      (mul_nonneg hβ (sq_nonneg _)) (countableBoundedFilter_bessel μ p β hβ hb D) =
        (countableContinuousPairAnalysis μ p hp β hβ hb).comp D.adjoint := by
  apply ContinuousLinearMap.ext
  intro q
  apply Lp.ext
  filter_upwards [countableContinuousPairAnalysis_ae μ (fun a => D (p a))
    (countableFilteredPair_coeff_memLp μ p hp D) (β*‖D‖^2)
    (mul_nonneg hβ (sq_nonneg _)) (countableBoundedFilter_bessel μ p β hβ hb D) q,
    countableContinuousPairAnalysis_ae μ p hp β hβ hb (D.adjoint q)] with a ha hb'
  change _ = (countableContinuousPairAnalysis μ p hp β hβ hb (D.adjoint q)) a
  rw [ha, hb', ContinuousLinearMap.adjoint_inner_right]

theorem countableBoundedFilter_operator :
    countableContinuousPairOperator μ (fun a => D (p a))
      (countableFilteredPair_coeff_memLp μ p hp D) (β*‖D‖^2)
      (mul_nonneg hβ (sq_nonneg _)) (countableBoundedFilter_bessel μ p β hβ hb D) =
        D.comp ((countableContinuousPairOperator μ p hp β hβ hb).comp D.adjoint) := by
  simp only [countableContinuousPairOperator, countableBoundedFilter_analysis μ p hp β hβ hb D,
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
    ContinuousLinearMap.comp_assoc]

/-- Arbitrary bounded filters, including inverse Gram roots which need not be contractions. -/
theorem countableBoundedFilter_energy
    (s : ℕ → Set α) (hc : AECover μ atTop s)
    (hloc : ∀ n, MemLp p 2 (μ.restrict (s n)))
    (hm : Monotone s) (hu : ⋃ n, s n = Set.univ) (N : ℕ) (x : countableSector N) :
    (∫ a, ‖countablePairAnnihilate N (D (p a)) x‖^2 ∂μ) =
      (inner ℂ x (countablePairLift N
        (D.comp ((countableContinuousPairOperator μ p hp β hβ hb).comp D.adjoint)) x)).re := by
  rw [← countableBoundedFilter_operator μ p hp β hβ hb D]
  exact (countableContinuousFrame_energy μ (fun a => D (p a))
    (countableFilteredPair_coeff_memLp μ p hp D) (β*‖D‖^2)
    (mul_nonneg hβ (sq_nonneg _)) (countableBoundedFilter_bessel μ p β hβ hb D)
    s hc (fun n => countableFilteredPair_local_memLp μ p D (s n) (hloc n)) hm hu N x).symm

end VortexGap.Fermion
