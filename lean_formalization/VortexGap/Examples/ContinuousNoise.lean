import VortexGap.Frame.ContinuousTwoNoiseBound
import VortexGap.Examples.ContinuousPhase

noncomputable section
set_option autoImplicit false
namespace VortexGap.Examples
open VortexGap.Fermion MeasureTheory OAI.LaughlinGap.Occupation
open scoped InnerProduct ComplexConjugate ENNReal

/-- The raw continuum pair bound is discharged, rather than assumed by the regression. -/
theorem phasePair_upper (q : PairSpace 2) :
    (inner ℂ q (continuousPairOperator phaseMeasure phasePair q)).re ≤ 1 * ‖q‖^2 := by
  rw [phasePair_operator, one_mul]
  have hn : ‖(InnerProductSpace.rankOne ℂ weightedUnitPair weightedUnitPair) q‖ ≤ ‖q‖ := by
    change ‖(inner ℂ weightedUnitPair q) • weightedUnitPair‖ ≤ _
    rw [norm_smul, weightedUnitPair_norm, mul_one]
    simpa only [weightedUnitPair_norm, one_mul] using norm_inner_le_norm weightedUnitPair q
  calc
    _ ≤ ‖q‖ * ‖(InnerProductSpace.rankOne ℂ weightedUnitPair weightedUnitPair) q‖ :=
      re_inner_le_norm (𝕜 := ℂ) q _
    _ ≤ ‖q‖ * ‖q‖ := mul_le_mul_of_nonneg_left hn (norm_nonneg q)
    _ = _ := by ring

theorem phasePair_defect (t : ℝ) :
    pairEmbed (exteriorSquare (lossDefect lossFilter).toLinearMap (phasePair t)) =
      (phaseScalar t * (16/25) : ℂ) • ket {0,1} := by
  have he : pairEmbed (exteriorSquare (lossDefect lossFilter).toLinearMap weightedUnitPair) =
      (16/25:ℂ) • ket {0,1} := by
    rw [lossFilter_defect, weightedUnitPair, exteriorSquare_wedge, pairEmbed_wedge]
    simp only [ContinuousLinearMap.coe_coe, smul_apply, one_apply_eq_self, create_smul,
      loss_basis_create, LinearMap.smul_apply, map_smul, loss_pair_created, smul_smul]
    norm_num
  rw [phasePair, map_smul, map_smul, he, smul_smul]

theorem phaseFilteredPair_annihilation (t : ℝ) :
    pairAnnihilate (phaseFilteredPair t) (ket {0,1}) =
      (conj (phaseScalar t) * (9/25) : ℂ) • ket ∅ := by
  rw [phaseFilteredPair, phasePair, map_smul, pairAnnihilate_smul,
    LinearMap.smul_apply, weighted_filtered_pair_base, smul_smul]

/-- Creation and annihilation carry opposite phases; the integral is genuinely nonzero. -/
theorem phaseTwoNoise_integrand (t : ℝ) :
    twoLossCreation lossFilter (phasePair t)
      (pairAnnihilate (phaseFilteredPair t) (ket {0,1})) =
        (144/625:ℂ) • fockProduct (ket {0,1}) (ket ∅) := by
  rw [twoLossCreation, phasePair_defect, phaseFilteredPair_annihilation]
  simp only [map_smul, LinearMap.smul_apply, smul_smul]
  have hc : conj (phaseScalar t) * phaseScalar t = 1 := by
    rw [Complex.conj_mul', phaseScalar_norm]
    norm_num
  congr 1
  calc
    _ = (144/625:ℂ) * (conj (phaseScalar t) * phaseScalar t) := by ring
    _ = _ := by rw [hc, mul_one]

theorem phaseTwoNoise_output :
    continuousTwoLossNoise lossFilter phaseMeasure phasePair (ket {0,1}) =
      (144/625:ℂ) • fockProduct (ket {0,1}) (ket ∅) := by
  rw [continuousTwoLossNoise_apply lossFilter phaseMeasure phasePair phasePair_memLp]
  change (∫ t, twoLossCreation lossFilter (phasePair t)
    (pairAnnihilate (phaseFilteredPair t) (ket {0,1})) ∂phaseMeasure) = _
  simp_rw [phaseTwoNoise_integrand]
  rw [integral_const, phaseMeasure_mass, one_smul]

theorem phaseTwoNoise_norm_sq :
    ‖continuousTwoLossNoise lossFilter phaseMeasure phasePair (ket {0,1})‖^2 = (20736/390625:ℝ) := by
  have hf : ‖(fockProduct (ket {0,1} : Space 2) (ket ∅ : Space 2))‖^2 = (1:ℝ) := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), fockProduct_inner]
    simp [inner_self_eq_norm_sq_to_K, ket_norm]
  rw [phaseTwoNoise_output, norm_smul, mul_pow]
  norm_num [hf]

/-- Instantiate the general continuum bound with every input proved; it is saturated. -/
theorem phaseTwoNoise_relative_instance :
    ‖continuousTwoLossNoise lossFilter phaseMeasure phasePair (ket {0,1})‖^2 ≤ (20736/390625:ℝ) := by
  have h := continuousTwoLossNoise_relative lossFilter phaseMeasure phasePair phasePair_memLp
    1 (by norm_num) phasePair_upper lossFilter_nonneg lossFilter_contraction (ket {0,1})
  change _ ≤ 1 * ‖1 - lossFilter^2‖^2 *
    (inner ℂ (ket {0,1}) (continuousFrameHamiltonian phaseMeasure phaseFilteredPair (ket {0,1}))).re at h
  rw [weighted_loss_delta, phaseFilteredPair_energy] at h
  norm_num at h ⊢
  exact h

end VortexGap.Examples

