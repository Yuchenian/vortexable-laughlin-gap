import VortexGap.Frame.CountableOneFrameFields
import VortexGap.Frame.CountableTwoFrameOverlap

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory VortexGap.Frame
open scoped InnerProduct ENNReal

/-- Raw trace-norm Schur rows control the concrete countable-mode one-environment
adjoint field on a finite-measure label region. -/
theorem countableOneFrame_local_schur_bessel
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (M : CountableOrbital →L[ℂ] CountableOrbital) (hc : ‖M‖ ≤ 1)
    (U : α → CountableTwoFrame)
    (hU0 : AEStronglyMeasurable (fun a => U a (PiLp.single 2 0 1)) μ)
    (hU1 : AEStronglyMeasurable (fun a => U a (PiLp.single 2 1 1)) μ)
    (ω : α → ℝ) (hω : ∀ a, 0 < ω a) (hωm : AEStronglyMeasurable ω μ)
    (C : ℝ) (hC : 0 ≤ C)
    (hrowInt : ∀ᵐ a ∂μ, Integrable
      (fun b => traceNormTwo (countableTwoFrameOverlap (U a) (U b)) * ω b) μ)
    (hrow : ∀ᵐ a ∂μ,
      (∫ b, traceNormTwo (countableTwoFrameOverlap (U a) (U b)) * ω b ∂μ) ≤ C * ω a)
    (y : CountableSpace) :
    (∫ a, ‖(countableOneFrameCreation M (U a (PiLp.single 2 0 1))
      (U a (PiLp.single 2 1 1))).adjoint y‖^2 ∂μ) ≤ C * ‖y‖^2 := by
  let u := fun a => U a (PiLp.single 2 0 1)
  let v := fun a => U a (PiLp.single 2 1 1)
  let R := fun a => countableOneFrameCreation M (u a) (v a)
  have hun : ∀ a, ‖u a‖ ≤ 1 := fun a => by simp [u]
  have hvn : ∀ a, ‖v a‖ ≤ 1 := fun a => by simp [v]
  have hR : MemLp R 2 μ := countableOneFrameCreation_memLp μ M u v hU0 hU1 hun hvn
  have hT : MemLp (fun a => (R a).adjoint) 2 μ :=
    countableOneFrameAdjoint_memLp μ M u v hU0 hU1 hun hvn
  let k := fun a b => ‖(R a).adjoint.comp (R b)‖
  have hkm : AEStronglyMeasurable (Function.uncurry k) (μ.prod μ) := by
    have hRa : AEStronglyMeasurable (fun z : α × α => R z.1) (μ.prod μ) :=
      hR.aestronglyMeasurable.comp_fst
    have hRb : AEStronglyMeasurable (fun z : α × α => R z.2) (μ.prod μ) :=
      hR.aestronglyMeasurable.comp_snd
    have hadj := (ContinuousLinearMap.adjoint : (CountableSpace →L[ℂ] CountableSpace) ≃ₗᵢ⋆[ℂ]
      (CountableSpace →L[ℂ] CountableSpace)).continuous.comp_aestronglyMeasurable hRa
    exact ((ContinuousLinearMap.compL ℂ CountableSpace CountableSpace CountableSpace).aestronglyMeasurable_comp₂
      hadj hRb).norm
  have hk (a b : α) : 0 ≤ k a b := norm_nonneg _
  have hs (a b : α) : k a b = k b a := by
    have h := ContinuousLinearMap.adjoint.norm_map ((R a).adjoint.comp (R b))
    simpa only [k, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint] using h.symm
  have hb (a b : α) : k a b * ω b ≤
      traceNormTwo (countableTwoFrameOverlap (U a) (U b)) * ω b :=
    mul_le_mul_of_nonneg_right (countableTwoFrame_overlap_norm_le M hc (U a) (U b)) (hω b).le
  have hki : ∀ᵐ a ∂μ, Integrable (fun b => k a b * ω b) μ := by
    filter_upwards [hrowInt, hkm.prodMk_left] with a hia hma
    apply hia.mono' (hma.mul hωm)
    exact Filter.Eventually.of_forall fun b => by
      change ‖k a b * ω b‖ ≤ _
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hk a b) (hω b).le)]
      exact hb a b
  have hkr : ∀ᵐ a ∂μ, (∫ b, k a b * ω b ∂μ) ≤ C * ω a := by
    filter_upwards [hki, hrowInt, hrow] with a hia hja hra
    exact (integral_mono_ae hia hja (Filter.Eventually.of_forall (hb a))).trans hra
  exact operatorAnalysis_schur_bessel μ (fun a => (R a).adjoint) hT
    k hk hs hkm ω hω hωm C hki hkr
    (fun a b => by simp only [ContinuousLinearMap.adjoint_adjoint]; exact le_refl _)
    hC y


section Global
variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ]
  (M : CountableOrbital →L[ℂ] CountableOrbital) (hc : ‖M‖ ≤ 1)
  (U : α → CountableTwoFrame)
  (hU0 : AEStronglyMeasurable (fun a => U a (PiLp.single 2 0 1)) μ)
  (hU1 : AEStronglyMeasurable (fun a => U a (PiLp.single 2 1 1)) μ)
  (ω : α → ℝ) (hω : ∀ a, 0 < ω a) (hωm : AEStronglyMeasurable ω μ)
  (C : ℝ) (hC : 0 ≤ C)
  (hrowInt : ∀ᵐ a ∂μ, Integrable
    (fun b => traceNormTwo (countableTwoFrameOverlap (U a) (U b)) * ω b) μ)
  (hrow : ∀ᵐ a ∂μ,
    (∫ b, traceNormTwo (countableTwoFrameOverlap (U a) (U b)) * ω b ∂μ) ≤ C * ω a)

include hc hU0 hU1 hω hωm hC hrowInt hrow in
/-- The global analysis bound follows from the original rows by restriction and exhaustion.
Neither global operator-norm integrability nor a synthesis bound is assumed. -/
theorem countableOneFrame_global_bessel (y : CountableSpace) :
    MemLp (fun a => (countableOneFrameCreation M (U a (PiLp.single 2 0 1))
      (U a (PiLp.single 2 1 1))).adjoint y) 2 μ ∧
    (∫ a, ‖(countableOneFrameCreation M (U a (PiLp.single 2 0 1))
      (U a (PiLp.single 2 1 1))).adjoint y‖^2 ∂μ) ≤ C * ‖y‖^2 := by
  let f := fun a => (countableOneFrameCreation M (U a (PiLp.single 2 0 1))
    (U a (PiLp.single 2 1 1))).adjoint y
  have hcov := increasingCutoffs_aecover μ (spanningSets μ)
    (measurableSet_spanningSets μ) (monotone_spanningSets μ) (iUnion_spanningSets μ)
  have hloc (n : ℕ) : MemLp f 2 (μ.restrict (spanningSets μ n)) := by
    haveI : IsFiniteMeasure (μ.restrict (spanningSets μ n)) :=
      isFiniteMeasure_restrict.mpr (measure_spanningSets_lt_top μ n).ne
    exact operatorApply_memLp _ _ (countableOneFrameAdjoint_memLp
      (μ.restrict (spanningSets μ n)) M _ _ hU0.restrict hU1.restrict
      (fun a => by simp) (fun a => by simp)) y
  have hbound (n : ℕ) :
      (∫ a in spanningSets μ n, ‖f a‖^2 ∂μ) ≤ C * ‖y‖^2 := by
    haveI : IsFiniteMeasure (μ.restrict (spanningSets μ n)) :=
      isFiniteMeasure_restrict.mpr (measure_spanningSets_lt_top μ n).ne
    have hi : ∀ᵐ a ∂(μ.restrict (spanningSets μ n)), Integrable
        (fun b => traceNormTwo (countableTwoFrameOverlap (U a) (U b)) * ω b)
        (μ.restrict (spanningSets μ n)) :=
      ae_restrict_of_ae (hrowInt.mono fun a ha => ha.restrict)
    have hr : ∀ᵐ a ∂(μ.restrict (spanningSets μ n)),
        (∫ b in spanningSets μ n,
          traceNormTwo (countableTwoFrameOverlap (U a) (U b)) * ω b ∂μ) ≤ C * ω a := by
      apply ae_restrict_of_ae
      filter_upwards [hrowInt,hrow] with a hi' hr'
      exact (integral_mono_measure Measure.restrict_le_self
        (Filter.Eventually.of_forall fun b =>
          mul_nonneg (traceNormTwo_nonneg _) (hω b).le) hi').trans hr'
    exact countableOneFrame_local_schur_bessel (μ.restrict (spanningSets μ n))
      M hc U hU0.restrict hU1.restrict ω hω hωm.restrict C hC hi hr y
  exact ⟨localL2_memLp μ _ hcov f hloc _ hbound,
    localL2_integral_le μ _ hcov f hloc _ hbound⟩

/-- The actual global adjoint-column analysis built from the raw trace-norm rows. -/
def countableContinuousOneAnalysis : CountableSpace →L[ℂ] Lp CountableSpace 2 μ :=
  besselAnalysis μ (fun a => (countableOneFrameCreation M
    (U a (PiLp.single 2 0 1)) (U a (PiLp.single 2 1 1))).adjoint)
    (fun y => (countableOneFrame_global_bessel μ M hc U hU0 hU1 ω hω hωm C hC hrowInt hrow y).1)
    C hC
    (fun y => (countableOneFrame_global_bessel μ M hc U hU0 hU1 ω hω hωm C hC hrowInt hrow y).2)

/-- Global synthesis is the genuine adjoint of the constructed analysis. -/
def countableContinuousOneSynthesis : Lp CountableSpace 2 μ →L[ℂ] CountableSpace :=
  (countableContinuousOneAnalysis μ M hc U hU0 hU1 ω hω hωm C hC hrowInt hrow).adjoint

theorem countableContinuousOneAnalysis_ae (y : CountableSpace) :
    countableContinuousOneAnalysis μ M hc U hU0 hU1 ω hω hωm C hC hrowInt hrow y =ᵐ[μ]
      fun a => (countableOneFrameCreation M (U a (PiLp.single 2 0 1))
        (U a (PiLp.single 2 1 1))).adjoint y :=
  besselAnalysis_ae μ _ _ _ _ _ y

theorem countableContinuousOneSynthesis_norm_sq (f : Lp CountableSpace 2 μ) :
    ‖countableContinuousOneSynthesis μ M hc U hU0 hU1 ω hω hωm C hC hrowInt hrow f‖^2 ≤
      C * ‖f‖^2 := by
  apply analysis_norm_sq_of_adjoint_bound _ C hC
  intro y
  rw [countableContinuousOneSynthesis, ContinuousLinearMap.adjoint_adjoint]
  rw [countableContinuousOneAnalysis, besselAnalysis_norm_sq]
  exact (countableOneFrame_global_bessel μ M hc U hU0 hU1 ω hω hωm C hC hrowInt hrow y).2

end Global

end VortexGap.Fermion

