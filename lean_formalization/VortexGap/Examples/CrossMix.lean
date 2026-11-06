import VortexGap.Examples.Cells

noncomputable section
set_option autoImplicit false
namespace VortexGap.Examples
open VortexGap.Fermion
open scoped BigOperators InnerProduct ComplexConjugate ComplexOrder

def crossMixVector : EuclideanSpace ℂ (Fin 4) := WithLp.toLp 2 ![3/5, 0, 4/5, 0]
def crossMixProjection : EuclideanSpace ℂ (Fin 4) →L[ℂ] EuclideanSpace ℂ (Fin 4) :=
  InnerProductSpace.rankOne ℂ crossMixVector crossMixVector
def crossMixFilter : EuclideanSpace ℂ (Fin 4) →L[ℂ] EuclideanSpace ℂ (Fin 4) :=
  1 - (1/100 : ℂ) • crossMixProjection

theorem crossMixVector_norm : ‖crossMixVector‖ = 1 := by
  have h : ‖crossMixVector‖^2 = 1 := by
    norm_num [EuclideanSpace.norm_sq_eq, crossMixVector, Fin.sum_univ_succ]
  nlinarith [norm_nonneg crossMixVector]

theorem crossMixProjection_nonneg : 0 ≤ crossMixProjection :=
  ContinuousLinearMap.nonneg_iff_isPositive.mpr (InnerProductSpace.isPositive_rankOne_self _)

theorem crossMixProjection_norm : ‖crossMixProjection‖ = 1 := by
  simp [crossMixProjection, crossMixVector_norm]

theorem crossMixProjection_square : crossMixProjection * crossMixProjection = crossMixProjection :=
  InnerProductSpace.isIdempotentElem_rankOne_self crossMixVector_norm

theorem crossMixFilter_nonneg : 0 ≤ crossMixFilter := by
  have hp : crossMixProjection ≤ 1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg _ crossMixProjection_nonneg).mp (by rw [crossMixProjection_norm])
  have ha := smul_nonneg (by norm_num [Complex.le_def] : (0 : ℂ) ≤ 99/100)
    (show (0 : EuclideanSpace ℂ (Fin 4) →L[ℂ] EuclideanSpace ℂ (Fin 4)) ≤ 1 from zero_le_one)
  have hb := smul_nonneg (by norm_num [Complex.le_def] : (0 : ℂ) ≤ 1/100) (sub_nonneg.mpr hp)
  have h := add_nonneg ha hb
  convert h using 1 <;> unfold crossMixFilter <;> module

theorem crossMixFilter_contraction : ‖crossMixFilter‖ ≤ 1 := by
  apply (CStarAlgebra.norm_le_one_iff_of_nonneg _ crossMixFilter_nonneg).mpr
  exact sub_le_self _ (smul_nonneg (by norm_num [Complex.le_def] : (0 : ℂ) ≤ 1/100) crossMixProjection_nonneg)

theorem crossMixFilter_defect_square :
    1 - crossMixFilter^2 = (199/10000 : ℂ) • crossMixProjection := by
  simp only [crossMixFilter, pow_two, sub_mul, mul_sub, one_mul, mul_one,
    smul_mul_assoc, mul_smul_comm, smul_smul, crossMixProjection_square]
  module

theorem crossMixFilter_delta : ‖1 - crossMixFilter^2‖ = (199/10000 : ℝ) := by
  rw [crossMixFilter_defect_square, norm_smul, crossMixProjection_norm]
  norm_num

theorem crossMixFilter_entry (i j : Fin 4) :
    crossMixFilter (PiLp.single 2 j 1) i =
      (if j=i then 1 else 0) - (1/100 : ℂ) * conj (crossMixVector j) * crossMixVector i := by
  simp [crossMixFilter, crossMixProjection, InnerProductSpace.rankOne_apply,
    EuclideanSpace.inner_single_right, PiLp.single_apply, smul_eq_mul, mul_assoc, eq_comm]

/-- This matrix element connects different cells (0,1) and (2,3). -/
theorem crossMixFilter_cross_cell : crossMixFilter (PiLp.single 2 0 1) 2 = (-3/625 : ℂ) := by
  rw [crossMixFilter_entry]
  change (0 : ℂ) - (1/100) * conj (3/5) * (4/5) = -3/625
  norm_num [map_ofNat]

theorem crossMixFilter_ne_identity : crossMixFilter ≠ 1 := by
  intro h
  have he := congrArg (fun T : EuclideanSpace ℂ (Fin 4) →L[ℂ] EuclideanSpace ℂ (Fin 4) =>
    T (PiLp.single 2 0 1) 2) h
  rw [crossMixFilter_cross_cell] at he
  norm_num at he

/-- All raw inputs of this finite toy model have been discharged. -/
theorem crossMix_gap {N : ℕ} {x : Space 4} (hx : InSector N x) :
    (9/10 : ℝ) * (inner ℂ x (filteredHamiltonian crossMixFilter (fun _ => 1) (cellPairs 2) x)).re ≤
      (inner ℂ x ((filteredHamiltonian crossMixFilter (fun _ => 1) (cellPairs 2) *
        filteredHamiltonian crossMixFilter (fun _ => 1) (cellPairs 2)) x)).re := by
  have h := cell_frame_transfer (k := 2) crossMixFilter crossMixFilter_nonneg crossMixFilter_contraction hx
  rw [crossMixFilter_delta] at h
  have he : 0 ≤ (inner ℂ x (filteredHamiltonian crossMixFilter (fun _ => 1) (cellPairs 2) x)).re := by
    rw [← filtered_frameAnalysis_norm_sq crossMixFilter (fun _ => 1) (by intro; norm_num)]
    exact sq_nonneg _
  nlinarith only [h, he]

/-- A nonzero energy checks that the instantiated inequality is not vacuous. -/
theorem crossMix_pair_energy :
    (inner ℂ (pairEmbed (cellPairs 2 0))
      (filteredHamiltonian crossMixFilter (fun _ => 1) (cellPairs 2) (pairEmbed (cellPairs 2 0)))).re =
      (2491/2500 : ℝ)^2 := by
  rw [filteredHamiltonian, frameHamiltonian_energy]
  simp only [Fin.sum_univ_two, one_mul, pairAnnihilate_pairEmbed, norm_smul, ket_norm, mul_one, cellPairs]
  simp only [exteriorSquare_pairBasis]
  simp only [pairBasis, EuclideanSpace.inner_single_right]
  simp only [wedgePair, WithLp.ofLp_toLp, ContinuousLinearMap.coe_coe, crossMixFilter_entry]
  norm_num [cellPair, crossMixVector, map_div₀, map_ofNat]

end VortexGap.Examples
