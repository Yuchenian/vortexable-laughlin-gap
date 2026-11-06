import VortexGap.Frame.CountableContinuousOneSchur
import VortexGap.Frame.SlaterSynthesis
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory VortexGap.Frame
open scoped InnerProduct ENNReal
variable {α I : Type*} [Fintype I]

def countableSlaterPair (c : I → ℂ) (U : I → CountableTwoFrame) : CountablePairSpace :=
  ∑ i, c i • countableWedge (U i (PiLp.single 2 0 1)) (U i (PiLp.single 2 1 1))

def countableSlaterColumn (M : CountableOrbital →L[ℂ] CountableOrbital)
    (c : I → ℂ) (U : I → CountableTwoFrame) : CountableSpace →L[ℂ] CountableSpace :=
  ∑ i, c i • countableOneFrameCreation M (U i (PiLp.single 2 0 1)) (U i (PiLp.single 2 1 1))

def countableSlaterKernel (c d : I → ℂ) (U V : I → CountableTwoFrame) : ℝ :=
  ∑ i, ∑ j, ‖c i‖ * ‖d j‖ * traceNormTwo (countableTwoFrameOverlap (U i) (V j))

theorem countableSlaterColumn_gram_le (M : CountableOrbital →L[ℂ] CountableOrbital) (hc : ‖M‖ ≤ 1)
    (c d : I → ℂ) (U V : I → CountableTwoFrame) :
    ‖(countableSlaterColumn M c U).adjoint ∘L countableSlaterColumn M d V‖ ≤ countableSlaterKernel c d U V := by
  apply (sumColumn_gram _ _ c d).trans
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_left (countableTwoFrame_overlap_norm_le M hc _ _) (by positivity)

variable [MeasurableSpace α] (μ : Measure α) (M : CountableOrbital →L[ℂ] CountableOrbital)
  (c : α → I → ℂ) (U : α → I → CountableTwoFrame)

theorem countableSlaterColumn_memLp (hl : ∀ i, MemLp (fun a => c a i) 2 μ)
    (hu : ∀ i (l : Fin 2), AEStronglyMeasurable (fun a => U a i (PiLp.single 2 l 1)) μ) :
    MemLp (fun a => countableSlaterColumn M (c a) (U a)) 2 μ := by
  unfold countableSlaterColumn
  refine memLp_finsetSum (f := fun (i : I) (a : α) => c a i • countableOneFrameCreation M
    (U a i (PiLp.single 2 0 1)) (U a i (PiLp.single 2 1 1))) Finset.univ ?_
  intro i _
  have hm := (countableOneFrameCreation_continuous M).comp_aestronglyMeasurable ((hu i 0).prodMk (hu i 1))
  apply (hl i).of_le_mul (c := 2*‖M‖) ((hl i).aestronglyMeasurable.smul hm)
  apply Filter.Eventually.of_forall
  intro a
  change ‖c a i • countableOneFrameCreation M _ _‖ ≤ _
  rw [norm_smul,mul_comm (2*‖M‖)]
  exact mul_le_mul_of_nonneg_left (countableOneFrameCreation_opNorm_bound M _ _ (by simp) (by simp)) (norm_nonneg _)

theorem countableSlaterAdjoint_memLp (hl : ∀ i, MemLp (fun a => c a i) 2 μ)
    (hu : ∀ i (l : Fin 2), AEStronglyMeasurable (fun a => U a i (PiLp.single 2 l 1)) μ) :
    MemLp (fun a => (countableSlaterColumn M (c a) (U a)).adjoint) 2 μ := by
  have hR := countableSlaterColumn_memLp μ M c U hl hu
  apply hR.of_le_mul (c := 1) ((ContinuousLinearMap.adjoint : (CountableSpace →L[ℂ] CountableSpace) ≃ₗᵢ⋆[ℂ]
    (CountableSpace →L[ℂ] CountableSpace)).continuous.comp_aestronglyMeasurable hR.aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun a => by simp

theorem countableSlater_local_bessel [IsFiniteMeasure μ] (hc : ‖M‖ ≤ 1)
    (hl : ∀ i, MemLp (fun a => c a i) 2 μ)
    (hu : ∀ i (l : Fin 2), AEStronglyMeasurable (fun a => U a i (PiLp.single 2 l 1)) μ)
    (ω : α → ℝ) (hω : ∀ a, 0 < ω a) (hωm : AEStronglyMeasurable ω μ)
    (C : ℝ) (hC : 0 ≤ C)
    (hrowInt : ∀ᵐ a ∂μ, Integrable (fun b => countableSlaterKernel (c a) (c b) (U a) (U b) * ω b) μ)
    (hrow : ∀ᵐ a ∂μ, (∫ b, countableSlaterKernel (c a) (c b) (U a) (U b) * ω b ∂μ) ≤ C * ω a)
    (y : CountableSpace) :
    (∫ a, ‖(countableSlaterColumn M (c a) (U a)).adjoint y‖^2 ∂μ) ≤ C*‖y‖^2 := by
  let R := fun a => countableSlaterColumn M (c a) (U a)
  have hR := countableSlaterColumn_memLp μ M c U hl hu
  have hT := countableSlaterAdjoint_memLp μ M c U hl hu
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
      countableSlaterKernel (c a) (c b) (U a) (U b) * ω b :=
    mul_le_mul_of_nonneg_right (countableSlaterColumn_gram_le M hc _ _ _ _) (hω b).le
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
variable [SigmaFinite μ] (hc : ‖M‖ ≤ 1)
    (hl : ∀ n i, MemLp (fun a => c a i) 2 (μ.restrict (spanningSets μ n)))
    (hu : ∀ i (l : Fin 2), AEStronglyMeasurable (fun a => U a i (PiLp.single 2 l 1)) μ)
    (ω : α → ℝ) (hω : ∀ a, 0 < ω a) (hωm : AEStronglyMeasurable ω μ)
    (C : ℝ) (hC : 0 ≤ C)
    (hrowInt : ∀ᵐ a ∂μ, Integrable (fun b => countableSlaterKernel (c a) (c b) (U a) (U b) * ω b) μ)
    (hrow : ∀ᵐ a ∂μ, (∫ b, countableSlaterKernel (c a) (c b) (U a) (U b) * ω b ∂μ) ≤ C * ω a)

include hc hl hu hω hωm hC hrowInt hrow in
theorem countableSlater_global_bessel (y : CountableSpace) :
    MemLp (fun a => (countableSlaterColumn M (c a) (U a)).adjoint y) 2 μ ∧
    (∫ a, ‖(countableSlaterColumn M (c a) (U a)).adjoint y‖^2 ∂μ) ≤ C*‖y‖^2 := by
  let f := fun a => (countableSlaterColumn M (c a) (U a)).adjoint y
  let K := fun a b => countableSlaterKernel (c a) (c b) (U a) (U b)
  have hk (a b : α) : 0 ≤ K a b := Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (traceNormTwo_nonneg _)
  have hcov := increasingCutoffs_aecover μ (spanningSets μ)
    (measurableSet_spanningSets μ) (monotone_spanningSets μ) (iUnion_spanningSets μ)
  have hloc (n : ℕ) : MemLp f 2 (μ.restrict (spanningSets μ n)) :=
    operatorApply_memLp _ _ (countableSlaterAdjoint_memLp _ M c U (hl n) (fun i l => (hu i l).restrict)) y
  have hbound (n : ℕ) : (∫ a in spanningSets μ n, ‖f a‖^2 ∂μ) ≤ C * ‖y‖^2 := by
    let ν := μ.restrict (spanningSets μ n)
    have : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr (measure_spanningSets_lt_top μ n).ne
    have hi : ∀ᵐ a ∂ν, Integrable (fun b => K a b * ω b) ν :=
      ae_restrict_of_ae (hrowInt.mono fun _ h => h.restrict)
    have hr : ∀ᵐ a ∂ν, (∫ b, K a b * ω b ∂ν) ≤ C*ω a := by
      apply ae_restrict_of_ae
      filter_upwards [hrowInt,hrow] with a hi' hr'
      exact (integral_mono_measure Measure.restrict_le_self
        (Filter.Eventually.of_forall fun b => mul_nonneg (hk a b) (hω b).le) hi').trans hr'
    exact countableSlater_local_bessel ν M c U hc (hl n) (fun i l => (hu i l).restrict)
      ω hω hωm.restrict C hC hi hr y
  exact ⟨localL2_memLp μ _ hcov f hloc _ hbound, localL2_integral_le μ _ hcov f hloc _ hbound⟩

def countableSlaterAnalysis : CountableSpace →L[ℂ] Lp CountableSpace 2 μ :=
  besselAnalysis μ (fun a => (countableSlaterColumn M (c a) (U a)).adjoint)
    (fun y => (countableSlater_global_bessel μ M c U hc hl hu ω hω hωm C hC hrowInt hrow y).1) C hC
    (fun y => (countableSlater_global_bessel μ M c U hc hl hu ω hω hωm C hC hrowInt hrow y).2)

theorem countableSlater_synthesis_bound (f : Lp CountableSpace 2 μ) :
    ‖(countableSlaterAnalysis μ M c U hc hl hu ω hω hωm C hC hrowInt hrow).adjoint f‖^2 ≤ C*‖f‖^2 := by
  apply analysis_norm_sq_of_adjoint_bound _ C hC
  intro y
  rw [ContinuousLinearMap.adjoint_adjoint,countableSlaterAnalysis,besselAnalysis_norm_sq]
  exact (countableSlater_global_bessel μ M c U hc hl hu ω hω hωm C hC hrowInt hrow y).2
end Global

end VortexGap.Fermion
