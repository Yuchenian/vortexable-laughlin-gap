import VortexGap.Frame.TwoNoiseBound
import VortexGap.Examples.LossOutput

noncomputable section
set_option autoImplicit false
namespace VortexGap.Examples
open VortexGap.Fermion OAI.LaughlinGap.Occupation
open scoped BigOperators InnerProduct ComplexConjugate ComplexOrder

def weightedUnitPair : PairSpace 2 := wedgePair (PiLp.single 2 0 1) (PiLp.single 2 1 1)
def weightedMeasure : Fin 2 → ℝ := ![1/4, 9/4]
def weightedPairs : Fin 2 → PairSpace 2 := ![weightedUnitPair, Complex.I • weightedUnitPair]

theorem weightedMeasure_nonneg (i : Fin 2) : 0 ≤ weightedMeasure i := by
  fin_cases i <;> norm_num [weightedMeasure]

theorem weightedUnitPair_embed : pairEmbed weightedUnitPair = ket {0,1} := by
  rw [weightedUnitPair, pairEmbed_wedge, loss_basis_create, loss_basis_create, loss_pair_created]

theorem weightedUnitPair_norm : ‖weightedUnitPair‖ = 1 := by
  rw [← pairEmbed_norm, weightedUnitPair_embed, ket_norm]

theorem weightedPairs_norm (i : Fin 2) : ‖weightedPairs i‖ = 1 := by
  fin_cases i <;> simp [weightedPairs, norm_smul, weightedUnitPair_norm]

/-- Unequal weights and a relative complex phase give destructive interference in S. -/
theorem weighted_synthesis_regression :
    pairSynthesis weightedMeasure weightedPairs (WithLp.toLp 2 ![1, Complex.I]) = -weightedUnitPair := by
  norm_num [pairSynthesis_apply, Fin.sum_univ_two, weightedMeasure, weightedPairs, smul_smul, mul_assoc]
  module

/-- The adjoint has the conjugate phase; the columns themselves stay normalized. -/
theorem weighted_adjoint_regression :
    (pairSynthesis weightedMeasure weightedPairs).adjoint weightedUnitPair =
      WithLp.toLp 2 ![(1/2:ℂ), -(3/2:ℂ)*Complex.I] := by
  ext i
  fin_cases i <;>
    norm_num [pairSynthesis_adjoint_apply, weightedMeasure, weightedPairs, inner_smul_left,
      inner_self_eq_norm_sq_to_K, weightedUnitPair_norm]

theorem weighted_pair_operator :
    (∑ i, (weightedMeasure i : ℂ) • pairRankOne (weightedPairs i)) =
      (5/2 : ℂ) • pairRankOne weightedUnitPair := by
  have hp : pairRankOne (Complex.I • weightedUnitPair) = pairRankOne weightedUnitPair := by
    apply LinearMap.ext
    intro q
    change (inner ℂ (Complex.I • weightedUnitPair) q) • (Complex.I • weightedUnitPair) =
      (inner ℂ weightedUnitPair q) • weightedUnitPair
    rw [inner_smul_left, smul_smul]
    congr 1
    simp only [Complex.conj_I]
    ring_nf
    simp
  norm_num [Fin.sum_univ_two, weightedMeasure, weightedPairs, hp]
  module

theorem weighted_pair_upper (q : PairSpace 2) :
    (inner ℂ q ((∑ i, (weightedMeasure i : ℂ) • pairRankOne (weightedPairs i)) q)).re ≤
      (5/2:ℝ) * ‖q‖^2 := by
  have hn : ‖pairRankOne weightedUnitPair q‖ ≤ ‖q‖ := by
    change ‖(inner ℂ weightedUnitPair q) • weightedUnitPair‖ ≤ _
    rw [norm_smul, weightedUnitPair_norm, mul_one]
    simpa only [weightedUnitPair_norm, one_mul] using norm_inner_le_norm weightedUnitPair q
  rw [weighted_pair_operator, LinearMap.smul_apply, inner_smul_right]
  norm_num [Complex.mul_re]
  calc
    _ ≤ ‖q‖ * ‖pairRankOne weightedUnitPair q‖ := re_inner_le_norm (𝕜 := ℂ) q _
    _ ≤ ‖q‖ * ‖q‖ := mul_le_mul_of_nonneg_left hn (norm_nonneg q)
    _ = _ := by ring

theorem weighted_filtered_pair_base :
    pairAnnihilate (exteriorSquare lossFilter.toLinearMap weightedUnitPair) (ket {0,1}) =
      (9/25:ℂ) • ket ∅ := by
  rw [weightedUnitPair, loss_filtered_annihilation]
  have ha := two_mode_pair
  change annihilateMode (1 : Fin 2) (annihilateMode 0 (ket {0,1})) = ket ∅ at ha
  rw [ha]

theorem weighted_filtered_pair_input :
    pairAnnihilate (exteriorSquare lossFilter.toLinearMap weightedUnitPair) (Complex.I • ket {0,1}) =
      (9/25 * Complex.I : ℂ) • ket ∅ := by
  rw [weightedUnitPair, loss_filtered_annihilation]
  have ha := two_mode_pair
  change annihilateMode (1 : Fin 2) (annihilateMode 0 (ket {0,1})) = ket ∅ at ha
  simp only [map_smul, ha, smul_smul]

theorem weighted_filtered_energy :
    (inner ℂ (Complex.I • ket {0,1})
      (filteredHamiltonian lossFilter weightedMeasure weightedPairs (Complex.I • ket {0,1}))).re = (81/250:ℝ) := by
  rw [filteredHamiltonian, frameHamiltonian_energy]
  norm_num [Fin.sum_univ_two, weightedMeasure, weightedPairs, map_smul,
    pairAnnihilate_smul, LinearMap.smul_apply, weighted_filtered_pair_base, norm_smul, ket_norm]

/-- Actual two-environment output, with both unequal-weight contributions nonzero. -/
theorem weighted_twoNoise_output :
    twoLossNoise lossFilter weightedMeasure weightedPairs (Complex.I • ket {0,1}) =
      (72/125 * Complex.I : ℂ) • fockProduct (ket {0,1}) (ket ∅) := by
  have he : pairEmbed (exteriorSquare (lossDefect lossFilter).toLinearMap weightedUnitPair) =
      (16/25:ℂ) • ket {0,1} := by
    rw [lossFilter_defect, weightedUnitPair, exteriorSquare_wedge, pairEmbed_wedge]
    simp only [ContinuousLinearMap.coe_coe, smul_apply, one_apply_eq_self, create_smul,
      loss_basis_create, LinearMap.smul_apply, map_smul, loss_pair_created, smul_smul]
    norm_num
  simp only [twoLossNoise, Fin.sum_univ_two, weightedMeasure, weightedPairs,
    Matrix.cons_val_zero, Matrix.cons_val_one, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.comp_apply, map_smul, pairAnnihilate_smul,
    weighted_filtered_pair_base, twoLossCreation, he, smul_smul]
  simp only [Complex.conj_I]
  rw [← add_smul]
  simp only [smul_smul]
  congr 1
  ring_nf
  norm_num
  ring

theorem weighted_loss_delta : ‖1 - lossFilter^2‖ = (16/25:ℝ) := by
  rw [← lossDefect_norm_sq lossFilter lossFilter_nonneg lossFilter_contraction, lossFilter_defect]
  norm_num [norm_smul]

theorem weighted_twoNoise_norm_sq :
    ‖twoLossNoise lossFilter weightedMeasure weightedPairs (Complex.I • ket {0,1})‖^2 = (5184/15625:ℝ) := by
  have hp : ‖(fockProduct (ket {0,1} : Space 2) (ket ∅ : Space 2))‖^2 = (1:ℝ) := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), fockProduct_inner]
    simp [inner_self_eq_norm_sq_to_K, ket_norm]
  rw [weighted_twoNoise_output, norm_smul, mul_pow]
  norm_num [norm_mul, hp]

/-- Apply the general relative theorem with every frame hypothesis discharged.
Its numerical upper bound equals the independently computed nonzero norm above. -/
theorem weighted_twoNoise_relative_instance :
    ‖twoLossNoise lossFilter weightedMeasure weightedPairs (Complex.I • ket {0,1})‖^2 ≤ (5184/15625:ℝ) := by
  have h := twoLossNoise_relative lossFilter lossFilter_nonneg lossFilter_contraction
    weightedMeasure weightedMeasure_nonneg weightedPairs (5/2) (by norm_num) weighted_pair_upper
    (Complex.I • ket {0,1})
  rw [weighted_loss_delta, weighted_filtered_energy] at h
  norm_num at h ⊢
  exact h

end VortexGap.Examples
