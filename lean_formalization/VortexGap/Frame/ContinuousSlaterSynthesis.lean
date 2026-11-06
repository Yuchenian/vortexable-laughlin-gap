import VortexGap.Frame.SlaterSynthesis
import VortexGap.Frame.ContinuousOneSynthesis
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory VortexGap.Frame
open scoped InnerProduct ENNReal
variable {n : ℕ} {X α : Type*} [MeasurableSpace X] [Fintype α]
  (μ : Measure X) (c : X → α → ℂ) (U : X → α → TwoFrame n)

private theorem weighted_frame_field {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    (L : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) →L[ℂ] G)
    (hc : ∀ a, MemLp (fun x => c x a) 2 μ)
    (hU : ∀ a (i : Fin 2), AEStronglyMeasurable (fun x => U x a (PiLp.single 2 i 1)) μ) :
    MemLp (fun x => ∑ a, c x a • L (U x a (PiLp.single 2 0 1)) (U x a (PiLp.single 2 1 1))) 2 μ := by
  apply memLp_finsetSum
  intro a _
  apply (hc a).of_le_mul (c := ‖L‖) ((hc a).aestronglyMeasurable.smul (L.aestronglyMeasurable_comp₂ (hU a 0) (hU a 1)))
  apply Filter.Eventually.of_forall
  intro x
  change ‖c x a • L (U x a (PiLp.single 2 0 1)) (U x a (PiLp.single 2 1 1))‖ ≤ _
  rw [norm_smul,mul_comm ‖L‖]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact (L.le_opNorm₂ _ _).trans_eq (by simp only [twoFrameColumn_norm,mul_one])

theorem continuousSlaterPair_memLp (hc : ∀ a, MemLp (fun x => c x a) 2 μ)
    (hU : ∀ a (i : Fin 2), AEStronglyMeasurable (fun x => U x a (PiLp.single 2 i 1)) μ) :
    MemLp (fun x => slaterPair (c x) (U x)) 2 μ :=
  weighted_frame_field μ c U (wedgePairField n) hc hU

theorem continuousSlaterColumn_memLp (M : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (hc : ∀ a, MemLp (fun x => c x a) 2 μ)
    (hU : ∀ a (i : Fin 2), AEStronglyMeasurable (fun x => U x a (PiLp.single 2 i 1)) μ) :
    MemLp (fun x => slaterColumn M (c x) (U x)) 2 μ :=
  weighted_frame_field μ c U (oneFrameCreationField M) hc hU

theorem continuousSlater_synthesis_le [SFinite μ]
    (M : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) (hc : ‖M‖ ≤ 1)
    (hcL : ∀ a, MemLp (fun x => c x a) 2 μ)
    (hU : ∀ a (i : Fin 2), AEStronglyMeasurable (fun x => U x a (PiLp.single 2 i 1)) μ)
    (ω : X → ℝ) (hω : ∀ a, 0 < ω a) (hωm : AEStronglyMeasurable ω μ)
    (C : ℝ)
    (hrowInt : ∀ᵐ a ∂μ, Integrable (fun b => slaterKernel (c a) (c b) (U a) (U b) * ω b) μ)
    (hrow : ∀ᵐ a ∂μ, (∫ b, slaterKernel (c a) (c b) (U a) (U b) * ω b ∂μ) ≤ C * ω a)
    (f : X → Space n) (hf : MemLp f 2 μ) :
    ‖∫ a, slaterColumn M (c a) (U a) (f a) ∂μ‖^2 ≤ C * ∫ a, ‖f a‖^2 ∂μ := by
  let R := fun a => slaterColumn M (c a) (U a)
  let k := fun a b => ‖(R a).adjoint.comp (R b)‖
  have hR : MemLp R 2 μ := continuousSlaterColumn_memLp μ c U M hcL hU
  have hkm : AEStronglyMeasurable (Function.uncurry k) (μ.prod μ) := by
    have hRa : AEStronglyMeasurable (fun z : X × X => R z.1) (μ.prod μ) := hR.aestronglyMeasurable.comp_fst
    have hRb : AEStronglyMeasurable (fun z : X × X => R z.2) (μ.prod μ) := hR.aestronglyMeasurable.comp_snd
    have hadj := (ContinuousLinearMap.adjoint : (Space n →L[ℂ] OrbitalStackSpace n) ≃ₗᵢ⋆[ℂ]
      (OrbitalStackSpace n →L[ℂ] Space n)).continuous.comp_aestronglyMeasurable
        hRa
    exact ((ContinuousLinearMap.compL ℂ (Space n) (OrbitalStackSpace n) (Space n)).aestronglyMeasurable_comp₂
      hadj hRb).norm
  have hk (a b : X) : 0 ≤ k a b := norm_nonneg _
  have hs (a b : X) : k a b = k b a := by
    have h := ContinuousLinearMap.adjoint.norm_map ((R a).adjoint.comp (R b))
    simpa only [k, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint] using h.symm
  have hb (a b : X) : k a b * ω b ≤ slaterKernel (c a) (c b) (U a) (U b) * ω b :=
    mul_le_mul_of_nonneg_right (slaterColumn_gram_le M hc _ _ _ _) (hω b).le
  have hki : ∀ᵐ a ∂μ, Integrable (fun b => k a b * ω b) μ := by
    filter_upwards [hrowInt, hkm.prodMk_left] with a hia hma
    apply hia.mono' (hma.mul hωm)
    exact Filter.Eventually.of_forall fun b => by
      change ‖k a b * ω b‖ ≤ slaterKernel (c a) (c b) (U a) (U b) * ω b
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hk a b) (hω b).le)]
      exact hb a b
  have hkr : ∀ᵐ a ∂μ, (∫ b, k a b * ω b ∂μ) ≤ C * ω a := by
    filter_upwards [hki, hrowInt, hrow] with a hia hja hra
    exact (integral_mono_ae hia hja (Filter.Eventually.of_forall (hb a))).trans hra
  apply integral_weighted_synthesis_norm_sq μ R f hf _ k hk hs hkm ω hω hωm C hki hkr (fun _ _ => le_rfl)
  apply (hR.norm.integrable_mul hf.norm).mono'
    ((ContinuousLinearMap.id ℂ (Space n →L[ℂ] OrbitalStackSpace n)).aestronglyMeasurable_comp₂
      hR.aestronglyMeasurable hf.aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun a => (R a).le_opNorm (f a)

end VortexGap.Fermion
