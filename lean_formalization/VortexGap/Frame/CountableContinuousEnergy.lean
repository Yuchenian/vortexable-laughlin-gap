import VortexGap.Frame.CountableContinuousAnalysis

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory Filter
open scoped InnerProduct ENNReal Topology
attribute [local instance] sectorOperatorNormed annihilationOperatorNormed

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)
  (p : α → CountablePairSpace)
  (hp : ∀ q, MemLp (fun a => inner ℂ (p a) q) 2 μ)
  (β : ℝ) (hβ : 0 ≤ β)
  (hb : ∀ q, (∫ a, ‖inner ℂ (p a) q‖^2 ∂μ) ≤ β * ‖q‖^2)
  (s : ℕ → Set α) (hc : AECover μ atTop s)
  (hloc : ∀ n, MemLp p 2 (μ.restrict (s n)))
  (hm : Monotone s) (hu : ⋃ n, s n = Set.univ)

include hc hloc hm hu in
/-- The weak pair operator has the actual global CAR energy form.
Only local Bochner integrals are used before taking the strong limit. -/
theorem countableContinuousFrame_energy (N : ℕ) (x : countableSector N) :
    (inner ℂ x (countablePairLift N
      (countableContinuousPairOperator μ p hp β hβ hb) x)).re =
      ∫ a, ‖countablePairAnnihilate N (p a) x‖^2 ∂μ := by
  have hf := countableFrameApply_memLp μ p hp β hβ hb s hc hloc N x
  have hi := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  have ht := hc.integral_tendsto_of_countably_generated hi
  have hl := countableContinuousPairLift_tendsto μ p hp β hβ hb s
    hc.measurableSet hm hu N x
  have hz : Tendsto (fun n => inner ℂ x (countablePairLift N
      (countableContinuousPairCutoff μ p hp β hβ hb (s n) (hc.measurableSet n)) x))
      atTop (𝓝 (inner ℂ x (countablePairLift N
        (countableContinuousPairOperator μ p hp β hβ hb) x))) :=
    tendsto_const_nhds.inner hl
  have hr := Complex.continuous_re.continuousAt.tendsto.comp hz
  have he (n : ℕ) :
      (inner ℂ x (countablePairLift N
        (countableContinuousPairCutoff μ p hp β hβ hb (s n) (hc.measurableSet n)) x)).re =
        ∫ a in s n, ‖countablePairAnnihilate N (p a) x‖^2 ∂μ := by
    rw [countableContinuousPairCutoff_integral μ p hp β hβ hb (s n)
      (hc.measurableSet n) (hloc n)]
    exact countableLocalFrame_energy (μ.restrict (s n)) p (hloc n) N x
  have hr' : Tendsto (fun n => ∫ a in s n, ‖countablePairAnnihilate N (p a) x‖^2 ∂μ)
      atTop (𝓝 ((inner ℂ x (countablePairLift N
        (countableContinuousPairOperator μ p hp β hβ hb) x)).re)) := by
    simpa only [Function.comp_def, he] using hr
  exact tendsto_nhds_unique hr' ht

include hm hu in
theorem countableContinuousFrameAnalysis_norm_sq (N : ℕ) (x : countableSector N) :
    ‖countableContinuousFrameAnalysis μ p hp β hβ hb s hc hloc N x‖^2 =
      (inner ℂ x (countablePairLift N
        (countableContinuousPairOperator μ p hp β hβ hb) x)).re := by
  rw [countableContinuousFrame_energy μ p hp β hβ hb s hc hloc hm hu N x]
  exact Frame.besselAnalysis_norm_sq μ _ _ _ _ _ x

include hm hu in
/-- The analysis Gram equals the concrete fixed-sector CAR Hamiltonian. -/
theorem countableContinuousFrameAnalysis_gram (N : ℕ) :
    (countableContinuousFrameAnalysis μ p hp β hβ hb s hc hloc N).adjoint.comp
      (countableContinuousFrameAnalysis μ p hp β hβ hb s hc hloc N) =
      countablePairLift N (countableContinuousPairOperator μ p hp β hβ hb) := by
  let A := countableContinuousFrameAnalysis μ p hp β hβ hb s hc hloc N
  let H := countablePairLift N (countableContinuousPairOperator μ p hp β hβ hb)
  have hH : H.IsPositive := countablePairLift_positive N _
    (countableContinuousPairOperator_positive μ p hp β hβ hb)
  have hG : (A.adjoint.comp A).IsPositive :=
    ContinuousLinearMap.isPositive_adjoint_comp_self A
  have he : (A.adjoint.comp A).toLinearMap = H.toLinearMap := by
    apply (ext_inner_map _ _).mp
    intro x
    rw [← hG.isSymmetric.coe_re_inner_apply_self x,
      ← hH.isSymmetric.coe_re_inner_apply_self x]
    congr 1
    rw [hG.isSymmetric x x, hH.isSymmetric x x]
    change (inner ℂ x (A.adjoint (A x))).re = (inner ℂ x (H x)).re
    rw [ContinuousLinearMap.adjoint_inner_right, ← RCLike.re_eq_complex_re,
      ← norm_sq_eq_re_inner (𝕜 := ℂ)]
    exact countableContinuousFrameAnalysis_norm_sq μ p hp β hβ hb s hc hloc hm hu N x
  exact ContinuousLinearMap.coe_injective he

end VortexGap.Fermion

