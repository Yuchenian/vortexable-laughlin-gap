import VortexGap.Frame.ContinuousSlaterSynthesis
import VortexGap.Frame.ContinuousOneNoiseBound
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory VortexGap.Frame
open scoped InnerProduct ENNReal ComplexOrder
variable {n : ℕ} {X α : Type*} [MeasurableSpace X] [Fintype α]
  (μ : Measure X) (c : X → α → ℂ) (U : X → α → TwoFrame n)
  (M : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))

/-- Integrated one-environment CAR output from a coherent local pair. -/
def continuousSlaterOneOutput (x : Space n) : SplitSpace n n :=
  ∫ t, (∑ a, c t a • oneLossCreation M (U t a (PiLp.single 2 0 1))
    (U t a (PiLp.single 2 1 1))) (pairAnnihilate (exteriorSquare M.toLinearMap (slaterPair (c t) (U t))) x) ∂μ

private theorem slater_action_ae (x : Space n)
    (hcL : ∀ a, MemLp (fun t => c t a) 2 μ)
    (hU : ∀ a (i : Fin 2), AEStronglyMeasurable (fun t => U t a (PiLp.single 2 i 1)) μ) :
    let q := fun t => exteriorSquare M.toLinearMap (slaterPair (c t) (U t))
    let z := continuousFrameAnalysis μ q (filteredPair_memLp M μ _ (continuousSlaterPair_memLp μ c U hcL hU)) x
    let L := LinearMap.toContinuousLinearMap (orbitalEnvironmentEmbed.comp (orbitalAmplify (lossDefect M)))
    (fun t => (∑ a, c t a • oneLossCreation M (U t a (PiLp.single 2 0 1))
    (U t a (PiLp.single 2 1 1))) (pairAnnihilate (exteriorSquare M.toLinearMap (slaterPair (c t) (U t))) x)) =ᵐ[μ] fun t => L (slaterColumn M (c t) (U t) (z t)) := by
  let q := fun t => exteriorSquare M.toLinearMap (slaterPair (c t) (U t))
  have hq : MemLp q 2 μ := filteredPair_memLp M μ _ (continuousSlaterPair_memLp μ c U hcL hU)
  let z := continuousFrameAnalysis μ q hq x
  let R := fun t => slaterColumn M (c t) (U t)
  let r := ∫ t, R t (z t) ∂μ
  let L := LinearMap.toContinuousLinearMap (orbitalEnvironmentEmbed.comp (orbitalAmplify (lossDefect M)))
  filter_upwards [continuousFrameAnalysis_ae μ q hq x] with t ht
  change z t = pairAnnihilate (q t) x at ht
  change _ = L (slaterColumn M (c t) (U t) (z t))
  rw [ht]
  simp only [slaterColumn,sum_apply,smul_apply,
    LinearMap.sum_apply, LinearMap.smul_apply,map_sum,map_smul,oneLossCreation_factorization]
  rfl


theorem continuousSlaterOneAction_integrable (x : Space n)
    (hcL : ∀ a, MemLp (fun t => c t a) 2 μ)
    (hU : ∀ a (i : Fin 2), AEStronglyMeasurable (fun t => U t a (PiLp.single 2 i 1)) μ) :
    Integrable (fun t => (∑ a, c t a • oneLossCreation M (U t a (PiLp.single 2 0 1))
    (U t a (PiLp.single 2 1 1))) (pairAnnihilate (exteriorSquare M.toLinearMap (slaterPair (c t) (U t))) x)) μ := by
  let q := fun t => exteriorSquare M.toLinearMap (slaterPair (c t) (U t))
  have hq : MemLp q 2 μ := filteredPair_memLp M μ _ (continuousSlaterPair_memLp μ c U hcL hU)
  let z := continuousFrameAnalysis μ q hq x
  let R := fun t => slaterColumn M (c t) (U t)
  let r := ∫ t, R t (z t) ∂μ
  let L := LinearMap.toContinuousLinearMap (orbitalEnvironmentEmbed.comp (orbitalAmplify (lossDefect M)))
  have hR := continuousSlaterColumn_memLp μ c U M hcL hU
  have hi : Integrable (fun t => R t (z t)) μ := by
    apply (hR.norm.integrable_mul (Lp.memLp z).norm).mono'
      ((ContinuousLinearMap.id ℂ (Space n →L[ℂ] OrbitalStackSpace n)).aestronglyMeasurable_comp₂
        hR.aestronglyMeasurable (Lp.aestronglyMeasurable z))
    exact Filter.Eventually.of_forall fun t => (R t).le_opNorm _
  exact (L.integrable_comp hi).congr (slater_action_ae μ c U M x hcL hU).symm

theorem continuousSlaterOneOutput_relative [SFinite μ] (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1)
    (hcL : ∀ a, MemLp (fun t => c t a) 2 μ)
    (hU : ∀ a (i : Fin 2), AEStronglyMeasurable (fun t => U t a (PiLp.single 2 i 1)) μ)
    (ω : X → ℝ) (hω : ∀ a, 0 < ω a) (hωm : AEStronglyMeasurable ω μ)
    (C : ℝ)
    (hrowInt : ∀ᵐ a ∂μ, Integrable (fun b => slaterKernel (c a) (c b) (U a) (U b) * ω b) μ)
    (hrow : ∀ᵐ a ∂μ, (∫ b, slaterKernel (c a) (c b) (U a) (U b) * ω b ∂μ) ≤ C * ω a)
    (x : Space n) :
    ‖continuousSlaterOneOutput μ c U M x‖^2 ≤ C*‖1-M^2‖*
      (inner ℂ x (continuousFrameHamiltonian μ (fun t => exteriorSquare M.toLinearMap (slaterPair (c t) (U t))) x)).re := by
  let q := fun t => exteriorSquare M.toLinearMap (slaterPair (c t) (U t))
  have hq : MemLp q 2 μ := filteredPair_memLp M μ _ (continuousSlaterPair_memLp μ c U hcL hU)
  let z := continuousFrameAnalysis μ q hq x
  let R := fun t => slaterColumn M (c t) (U t)
  let r := ∫ t, R t (z t) ∂μ
  let L := LinearMap.toContinuousLinearMap (orbitalEnvironmentEmbed.comp (orbitalAmplify (lossDefect M)))
  have hR := continuousSlaterColumn_memLp μ c U M hcL hU
  have hi : Integrable (fun t => R t (z t)) μ := by
    apply (hR.norm.integrable_mul (Lp.memLp z).norm).mono'
      ((ContinuousLinearMap.id ℂ (Space n →L[ℂ] OrbitalStackSpace n)).aestronglyMeasurable_comp₂
        hR.aestronglyMeasurable (Lp.aestronglyMeasurable z))
    exact Filter.Eventually.of_forall fun t => (R t).le_opNorm _
  have hout : continuousSlaterOneOutput μ c U M x = L r := by
    rw [continuousSlaterOneOutput, show L r = ∫ t, L (R t (z t)) ∂μ from (L.integral_comp_comm hi).symm]
    apply integral_congr_ae
    exact slater_action_ae μ c U M x hcL hU
  rw [hout]
  change ‖orbitalEnvironmentEmbed (orbitalAmplify (lossDefect M) r)‖^2 ≤ _
  rw [orbitalEnvironmentEmbed_norm_sq]
  have ha := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
    (orbitalAmplify_norm_le (lossDefect M) r)
  rw [mul_pow,lossDefect_norm_sq M hM hc] at ha
  have hs := continuousSlater_synthesis_le μ c U M hc hcL hU ω hω hωm C hrowInt hrow z (Lp.memLp z)
  rw [← Frame.l2_norm_sq_integral μ z] at hs
  have hz := continuousFrameAnalysis_energy μ q hq x
  change ‖z‖^2 = _ at hz
  exact ha.trans ((mul_le_mul_of_nonneg_left hs (norm_nonneg _)).trans_eq (by rw [hz]; ring))

end VortexGap.Fermion
