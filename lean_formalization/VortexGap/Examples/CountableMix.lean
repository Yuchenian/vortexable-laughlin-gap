import VortexGap.Examples.CountableModeFrame
noncomputable section
set_option autoImplicit false
namespace VortexGap.Examples
open VortexGap.Fermion
open scoped InnerProduct ComplexOrder ComplexConjugate

def countableMixVector : CountableOrbital :=
  (3/5 : ℂ) • orbitalKet 0 + (4/5 : ℂ) • orbitalKet 2
def countableMixProjection : CountableOrbital →L[ℂ] CountableOrbital :=
  InnerProductSpace.rankOne ℂ countableMixVector countableMixVector
def countableMixFilter : CountableOrbital →L[ℂ] CountableOrbital :=
  1 - (1/100 : ℂ) • countableMixProjection

theorem countableMixVector_apply (i : ℕ) :
    countableMixVector i = (if i=0 then (3/5 : ℂ) else 0) + (if i=2 then (4/5 : ℂ) else 0) := by
  change (3/5 : ℂ) * orbitalKet 0 i + (4/5 : ℂ) * orbitalKet 2 i = _
  simp [orbitalKet, lp.single_apply, Pi.single_apply, eq_comm]

theorem countableMixVector_norm : ‖countableMixVector‖ = 1 := by
  have h : ‖countableMixVector‖^2 = 1 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
    change (inner ℂ ((3/5 : ℂ) • orbitalKet 0 + (4/5 : ℂ) • orbitalKet 2)
      ((3/5 : ℂ) • orbitalKet 0 + (4/5 : ℂ) • orbitalKet 2)).re = 1
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, orbitalKet_inner_left]
    norm_num [orbitalKet, lp.single_apply, map_ofNat]
  nlinarith [norm_nonneg countableMixVector]

theorem countableMixProjection_nonneg : 0 ≤ countableMixProjection :=
  ContinuousLinearMap.nonneg_iff_isPositive.mpr (InnerProductSpace.isPositive_rankOne_self _)

theorem countableMixProjection_norm : ‖countableMixProjection‖ = 1 := by
  simp [countableMixProjection, countableMixVector_norm]

theorem countableMixProjection_square :
    countableMixProjection * countableMixProjection = countableMixProjection :=
  InnerProductSpace.isIdempotentElem_rankOne_self countableMixVector_norm

theorem countableMixFilter_nonneg : 0 ≤ countableMixFilter := by
  have hp : countableMixProjection ≤ 1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg _ countableMixProjection_nonneg).mp
      (by rw [countableMixProjection_norm])
  have ha : (0 : CountableOrbital →L[ℂ] CountableOrbital) ≤ (99/100 : ℂ) • 1 :=
    smul_nonneg (by norm_num [Complex.le_def] : (0 : ℂ) ≤ 99/100)
      (show (0 : CountableOrbital →L[ℂ] CountableOrbital) ≤ 1 from zero_le_one)
  have hb : (0 : CountableOrbital →L[ℂ] CountableOrbital) ≤
      (1/100 : ℂ) • (1-countableMixProjection) :=
    smul_nonneg (by norm_num [Complex.le_def] : (0 : ℂ) ≤ 1/100) (sub_nonneg.mpr hp)
  have h := add_nonneg ha hb
  convert h using 1 <;> unfold countableMixFilter <;> module

theorem countableMixFilter_contraction : ‖countableMixFilter‖ ≤ 1 := by
  apply (CStarAlgebra.norm_le_one_iff_of_nonneg _ countableMixFilter_nonneg).mpr
  exact sub_le_self _ (smul_nonneg (by norm_num [Complex.le_def] : (0 : ℂ) ≤ 1/100)
    countableMixProjection_nonneg)

theorem countableMixFilter_defect :
    1-countableMixFilter^2 = (199/10000 : ℂ) • countableMixProjection := by
  simp only [countableMixFilter, pow_two, sub_mul, mul_sub, one_mul, mul_one,
    smul_mul_assoc, mul_smul_comm, smul_smul, countableMixProjection_square]
  module

theorem countableMixFilter_delta : ‖1-countableMixFilter^2‖ = (199/10000 : ℝ) := by
  rw [countableMixFilter_defect, norm_smul, countableMixProjection_norm]
  norm_num

theorem countableMixFilter_entry (i j : ℕ) :
    countableMixFilter (orbitalKet j) i =
      (if j=i then 1 else 0) -
        (1/100 : ℂ) * conj (countableMixVector j) * countableMixVector i := by
  change orbitalKet j i - (1/100 : ℂ) *
    (inner ℂ countableMixVector (orbitalKet j) * countableMixVector i) = _
  have hi : inner ℂ countableMixVector (orbitalKet j) = conj (countableMixVector j) := by
    simp [orbitalKet, lp.inner_single_right, RCLike.inner_apply]
  rw [hi]
  simp [orbitalKet, lp.single_apply, Pi.single_apply, eq_comm, mul_assoc]

theorem countableMixFilter_offDiagonal :
    countableMixFilter (orbitalKet 0) 2 = (-3/625 : ℂ) := by
  rw [countableMixFilter_entry]
  norm_num [countableMixVector_apply, map_ofNat]

theorem countableMixFilter_ne_identity : countableMixFilter ≠ 1 := by
  intro h
  have he := congrArg (fun T : CountableOrbital →L[ℂ] CountableOrbital => T (orbitalKet 0) 2) h
  rw [countableMixFilter_offDiagonal] at he
  norm_num [orbitalKet, lp.single_apply, map_ofNat] at he

def countableMixPair : CountablePairSpace :=
  countableWedge (countableMixFilter (orbitalKet 0)) (countableMixFilter (orbitalKet 1))
def countableMixHamiltonian (N : ℕ) : countableSector N →L[ℂ] countableSector N :=
  countablePairLift N (InnerProductSpace.rankOne ℂ countableMixPair countableMixPair)

theorem countableMixHamiltonian_positive (N : ℕ) : (countableMixHamiltonian N).IsPositive :=
  countablePairLift_positive N _ (InnerProductSpace.isPositive_rankOne_self _)

/-- Closed changed-filter regression on every complete fixed-N sector, with infinitely many
available spectator orbitals. The reference gap is proved, not supplied by the caller. -/
theorem countableMix_gap_norm (N : ℕ) (x : countableSector N) :
    (9/10 : ℝ) * (inner ℂ x (countableMixHamiltonian N x)).re ≤
      ‖countableMixHamiltonian N x‖^2 := by
  have h := countable_single_pair_transfer ⟨(0,1), by decide⟩ countableMixFilter
    countableMixFilter_nonneg countableMixFilter_contraction N
  change (countableMixHamiltonian N * countableMixHamiltonian N -
    ((1-2*‖1-countableMixFilter^2‖-‖1-countableMixFilter^2‖^2 : ℝ) : ℂ) •
      countableMixHamiltonian N).IsPositive at h
  have hn := (VortexGap.quadratic_positive_norm_iff _ (countableMixHamiltonian_positive N) _).mp h x
  rw [countableMixFilter_delta] at hn
  have he := (countableMixHamiltonian_positive N).re_inner_nonneg_right x
  nlinarith only [hn,he]

theorem countableMix_gap (N : ℕ) :
    (countableMixHamiltonian N * countableMixHamiltonian N -
      (9/10 : ℂ) • countableMixHamiltonian N).IsPositive := by
  have h := (VortexGap.quadratic_positive_norm_iff _ (countableMixHamiltonian_positive N)
    (9/10 : ℝ)).mpr (countableMix_gap_norm N)
  norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat] at h
  exact h

theorem countableMixPair_coefficient :
    countableMixPair ⟨(0,1), by decide⟩ = (2491/2500 : ℂ) := by
  rw [countableMixPair, countableWedge_coordinate]
  simp only [countableMixFilter_entry]
  norm_num [countableMixVector_apply, map_ofNat]

def countableMixTest : countableSector 2 :=
  ⟨countablePairEmbedding (lp.single 2 ⟨(0,1), by decide⟩ 1),
    countablePairEmbedding_sector _⟩

theorem countableMix_energy :
    (inner ℂ countableMixTest (countableMixHamiltonian 2 countableMixTest)).re =
      (2491/2500 : ℝ)^2 := by
  rw [countableMixHamiltonian, countableMixTest, countablePairLift_pairEmbedding]
  change (inner ℂ (countablePairEmbedding (lp.single 2 ⟨(0,1), by decide⟩ 1))
    (countablePairEmbedding (InnerProductSpace.rankOne ℂ countableMixPair countableMixPair
      (lp.single 2 ⟨(0,1), by decide⟩ 1)))).re = _
  rw [countablePairEmbedding.inner_map_map, InnerProductSpace.rankOne_apply, inner_smul_right]
  norm_num [lp.inner_single_left, lp.inner_single_right, RCLike.inner_apply,
    countableMixPair_coefficient, map_ofNat]

theorem countableMixHamiltonian_nonzero : countableMixHamiltonian 2 ≠ 0 := by
  intro h
  have he := countableMix_energy
  rw [h] at he
  norm_num at he
end VortexGap.Examples
