import VortexGap.Frame.ContinuousFrameFields
import VortexGap.Frame.ContinuousSchurOperator
import VortexGap.Frame.L2FiniteFiber

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory VortexGap.Frame
open scoped InnerProduct ENNReal

theorem twoFrameColumn_norm {n : ℕ} (U : TwoFrame n) (i : Fin 2) :
    ‖U (PiLp.single 2 i 1)‖ = 1 := by simp

variable {n : ℕ}
  (M : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
  {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
  (u v : α → EuclideanSpace ℂ (Fin n))
  (hu : AEStronglyMeasurable u μ) (hv : AEStronglyMeasurable v μ)
  (hun : ∀ a, ‖u a‖ ≤ 1) (hvn : ∀ a, ‖v a‖ ≤ 1)

include hu hv hun hvn in
theorem oneFrameAdjoint_memLp :
    MemLp (fun a => (LinearMap.toContinuousLinearMap (oneFrameCreation M (u a) (v a))).adjoint) 2 μ := by
  have hR := oneFrameCreation_memLp M μ u v hu hv hun hvn
  apply hR.of_le_mul (c := 1)
    ((ContinuousLinearMap.adjoint : (Space n →L[ℂ] OrbitalStackSpace n) ≃ₗᵢ⋆[ℂ]
      (OrbitalStackSpace n →L[ℂ] Space n)).continuous.comp_aestronglyMeasurable hR.aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun a => by
    rw [ContinuousLinearMap.adjoint.norm_map, one_mul]

/-- Actual quotient-L2 synthesis, constructed independently of its Schur estimate. -/
def continuousOneFrameSynthesis : Lp (Space n) 2 μ →L[ℂ] OrbitalStackSpace n :=
  (Frame.operatorAnalysis μ
    (fun a => (LinearMap.toContinuousLinearMap (oneFrameCreation M (u a) (v a))).adjoint)
    (oneFrameAdjoint_memLp M μ u v hu hv hun hvn)).adjoint

theorem continuousOneFrameSynthesis_apply (f : Lp (Space n) 2 μ) :
    continuousOneFrameSynthesis M μ u v hu hv hun hvn f =
      ∫ a, oneFrameCreation M (u a) (v a) (f a) ∂μ := by
  rw [continuousOneFrameSynthesis, Frame.operatorAnalysis_adjoint_apply]
  simp only [ContinuousLinearMap.adjoint_adjoint, LinearMap.coe_toContinuousLinearMap']

theorem continuousOneFrameSynthesis_representative (f : Lp (Space n) 2 μ) (g : α → Space n)
    (heq : f =ᵐ[μ] g) : continuousOneFrameSynthesis M μ u v hu hv hun hvn f =
      ∫ a, oneFrameCreation M (u a) (v a) (g a) ∂μ := by
  rw [continuousOneFrameSynthesis_apply]
  apply integral_congr_ae
  filter_upwards [heq] with a ha
  rw [ha]

/-- Raw one-particle trace-norm rows imply the bound on the actual CAR synthesis. -/
theorem continuousOneFrameSynthesis_norm_sq_le (hc : ‖M‖ ≤ 1) (U : α → TwoFrame n)
    (hU0 : AEStronglyMeasurable (fun a => U a (PiLp.single 2 0 1)) μ)
    (hU1 : AEStronglyMeasurable (fun a => U a (PiLp.single 2 1 1)) μ)
    (ω : α → ℝ) (hω : ∀ a, 0 < ω a) (hωm : AEStronglyMeasurable ω μ)
    (C : ℝ)
    (hrowInt : ∀ᵐ a ∂μ, Integrable (fun b => traceNormTwo (twoFrameOverlap (U a) (U b)) * ω b) μ)
    (hrow : ∀ᵐ a ∂μ, (∫ b, traceNormTwo (twoFrameOverlap (U a) (U b)) * ω b ∂μ) ≤ C * ω a)
    (f : Lp (Space n) 2 μ) :
    ‖continuousOneFrameSynthesis M μ (fun a => U a (PiLp.single 2 0 1))
      (fun a => U a (PiLp.single 2 1 1)) hU0 hU1
      (fun a => (twoFrameColumn_norm (U a) 0).le) (fun a => (twoFrameColumn_norm (U a) 1).le) f‖^2 ≤
      C * ‖f‖^2 := by
  let u := fun a => U a (PiLp.single 2 0 1)
  let v := fun a => U a (PiLp.single 2 1 1)
  let R := fun a => LinearMap.toContinuousLinearMap (oneFrameCreation M (u a) (v a))
  let k := fun a b => ‖(R a).adjoint.comp (R b)‖
  have hR : MemLp R 2 μ := oneFrameCreation_memLp M μ u v hU0 hU1
    (fun a => (twoFrameColumn_norm (U a) 0).le) (fun a => (twoFrameColumn_norm (U a) 1).le)
  have hkm : AEStronglyMeasurable (Function.uncurry k) (μ.prod μ) := by
    have hRa : AEStronglyMeasurable (fun z : α × α => R z.1) (μ.prod μ) := hR.aestronglyMeasurable.comp_fst
    have hRb : AEStronglyMeasurable (fun z : α × α => R z.2) (μ.prod μ) := hR.aestronglyMeasurable.comp_snd
    have hadj := (ContinuousLinearMap.adjoint : (Space n →L[ℂ] OrbitalStackSpace n) ≃ₗᵢ⋆[ℂ]
      (OrbitalStackSpace n →L[ℂ] Space n)).continuous.comp_aestronglyMeasurable
        hRa
    exact ((ContinuousLinearMap.compL ℂ (Space n) (OrbitalStackSpace n) (Space n)).aestronglyMeasurable_comp₂
      hadj hRb).norm
  have hk (a b : α) : 0 ≤ k a b := norm_nonneg _
  have hs (a b : α) : k a b = k b a := by
    have h := ContinuousLinearMap.adjoint.norm_map ((R a).adjoint.comp (R b))
    simpa only [k, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint] using h.symm
  have hb (a b : α) : k a b * ω b ≤ traceNormTwo (twoFrameOverlap (U a) (U b)) * ω b :=
    mul_le_mul_of_nonneg_right (twoFrame_overlap_norm_le M hc (U a) (U b)) (hω b).le
  have hki : ∀ᵐ a ∂μ, Integrable (fun b => k a b * ω b) μ := by
    filter_upwards [hrowInt, hkm.prodMk_left] with a hia hma
    apply hia.mono' (hma.mul hωm)
    exact Filter.Eventually.of_forall fun b => by
      change ‖k a b * ω b‖ ≤ traceNormTwo (twoFrameOverlap (U a) (U b)) * ω b
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hk a b) (hω b).le)]
      exact hb a b
  have hkr : ∀ᵐ a ∂μ, (∫ b, k a b * ω b ∂μ) ≤ C * ω a := by
    filter_upwards [hki, hrowInt, hrow] with a hia hja hra
    exact (integral_mono_ae hia hja (Filter.Eventually.of_forall (hb a))).trans hra
  rw [continuousOneFrameSynthesis_apply, Frame.l2_norm_sq_integral μ f]
  exact integral_weighted_synthesis_norm_sq μ R f (Lp.memLp f)
    (oneFrameCreation_apply_integrable M μ u v hU0 hU1
      (fun a => (twoFrameColumn_norm (U a) 0).le) (fun a => (twoFrameColumn_norm (U a) 1).le) f)
    k hk hs hkm ω hω hωm C hki hkr (fun _ _ => le_refl _)

end VortexGap.Fermion

