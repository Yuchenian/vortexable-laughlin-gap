import VortexGap.Frame.CountableContinuousEnergy
import VortexGap.Fermion.CountablePairCompression

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory
open scoped InnerProduct ENNReal ComplexOrder
variable {α : Type*} [MeasurableSpace α] (μ : Measure α) (p : α → CountablePairSpace)
  (hp : ∀ q, MemLp (fun a => inner ℂ (p a) q) 2 μ)
  (β : ℝ) (hβ : 0 ≤ β)
  (hb : ∀ q, (∫ a, ‖inner ℂ (p a) q‖^2 ∂μ) ≤ β * ‖q‖^2)
  (F : CountablePairSpace →L[ℂ] CountablePairSpace) (hF : ‖F‖ ≤ 1)

include hp in
theorem countableFilteredPair_coeff_memLp (q : CountablePairSpace) :
    MemLp (fun a => inner ℂ (F (p a)) q) 2 μ := by
  simpa only [← ContinuousLinearMap.adjoint_inner_right] using hp (F.adjoint q)

include hβ hb hF in
theorem countableFilteredPair_bessel (q : CountablePairSpace) :
    (∫ a, ‖inner ℂ (F (p a)) q‖^2 ∂μ) ≤ β * ‖q‖^2 := by
  have hn : ‖F.adjoint q‖ ≤ ‖q‖ := by
    have hf : ‖F.adjoint‖ ≤ 1 := by simpa only [ContinuousLinearMap.adjoint.norm_map] using hF
    simpa only [one_mul] using F.adjoint.le_of_opNorm_le hf q
  calc
    _ = ∫ a, ‖inner ℂ (p a) (F.adjoint q)‖^2 ∂μ := by
      congr 1
      funext a
      rw [ContinuousLinearMap.adjoint_inner_right]
    _ ≤ β * ‖F.adjoint q‖^2 := hb _
    _ ≤ β * ‖q‖^2 := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) hn 2) hβ

theorem countableFilteredPair_local_memLp (s : Set α)
    (hloc : MemLp p 2 (μ.restrict s)) :
    MemLp (fun a => F (p a)) 2 (μ.restrict s) :=
  F.comp_memLp' hloc

theorem countableFilteredPair_analysis :
    countableContinuousPairAnalysis μ (fun a => F (p a))
      (countableFilteredPair_coeff_memLp μ p hp F) β hβ
      (countableFilteredPair_bessel μ p β hβ hb F hF) =
    (countableContinuousPairAnalysis μ p hp β hβ hb).comp F.adjoint := by
  apply ContinuousLinearMap.ext
  intro q
  apply Lp.ext
  filter_upwards [
    countableContinuousPairAnalysis_ae μ (fun a => F (p a))
      (countableFilteredPair_coeff_memLp μ p hp F) β hβ
      (countableFilteredPair_bessel μ p β hβ hb F hF) q,
    countableContinuousPairAnalysis_ae μ p hp β hβ hb (F.adjoint q)] with a ha hb'
  change _ = (countableContinuousPairAnalysis μ p hp β hβ hb (F.adjoint q)) a
  rw [ha, hb', ContinuousLinearMap.adjoint_inner_right]

theorem countableFilteredPair_operator :
    countableContinuousPairOperator μ (fun a => F (p a))
      (countableFilteredPair_coeff_memLp μ p hp F) β hβ
      (countableFilteredPair_bessel μ p β hβ hb F hF) =
    F.comp ((countableContinuousPairOperator μ p hp β hβ hb).comp F.adjoint) := by
  simp only [countableContinuousPairOperator,
    countableFilteredPair_analysis μ p hp β hβ hb F hF,
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
    ContinuousLinearMap.comp_assoc]

end VortexGap.Fermion
