import VortexGap.Fermion.NumberParity
import VortexGap.Operator.LossDefect

/-! Exact, non-real four-mode pair regressions. These are not a gap-transfer example. -/
noncomputable section
set_option autoImplicit false
namespace VortexGap.Examples
open VortexGap.Fermion OAI.LaughlinGap.Occupation
open scoped InnerProduct ComplexConjugate ComplexOrder

def pair01 : PairIndex 4 := ⟨(0, 1), by decide⟩
def pair23 : PairIndex 4 := ⟨(2, 3), by decide⟩

/-- Two distinct pairs with a non-real relative phase, unit l2 norm. -/
def mixedPair : PairSpace 4 :=
  (3 / 5 : ℂ) • pairBasis pair01 + (4 / 5 * Complex.I : ℂ) • pairBasis pair23

theorem mixedPair_inner : inner ℂ mixedPair mixedPair = 1 := by
  simp only [mixedPair, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right]
  norm_num [pairBasis, EuclideanSpace.inner_single_left, PiLp.single_apply, pair01, pair23,
    map_ofNat]
  ring_nf
  norm_num

theorem mixedPair_annihilation :
    pairAnnihilate mixedPair (pairEmbed mixedPair) = ket ∅ := by
  rw [pairAnnihilate_pairEmbed, mixedPair_inner, one_smul]

theorem mixedPair_projector :
    pairLift (pairRankOne mixedPair) (pairEmbed mixedPair) = pairEmbed mixedPair := by
  rw [pairLift_pairEmbed]
  change pairEmbed ((inner ℂ mixedPair mixedPair) • mixedPair) = _
  rw [mixedPair_inner, one_smul]

theorem mixedPair_parity : parity 4 (pairEmbed mixedPair) = pairEmbed mixedPair := by
  rw [parity_on_sector (pairEmbed_sector mixedPair)]
  norm_num

theorem three_particle_parity :
    parity 4 (ket {0, 1, 2}) = -(ket {0, 1, 2} : Space 4) := by
  rw [parity_on_sector (sector_ket {0, 1, 2})]
  norm_num

theorem mixedPair_full_occupation :
    pairAnnihilate mixedPair (ket Finset.univ) =
      (3 / 5 : ℂ) • ket {2, 3} - (4 / 5 * Complex.I : ℂ) • ket {0, 1} := by
  have ha : pairAnnihilate mixedPair =
      (3 / 5 : ℂ) • pairMode pair01 - (4 / 5 * Complex.I : ℂ) • pairMode pair23 := by
    have hadd (p q : PairSpace 4) :
        pairAnnihilate (p + q) = pairAnnihilate p + pairAnnihilate q := by
      simp [pairAnnihilate, add_smul, Finset.sum_add_distrib]
    have hb (a : PairIndex 4) : pairAnnihilate (pairBasis a) = pairMode a := by
      unfold pairAnnihilate
      rw [Finset.sum_eq_single a]
      · simp [pairBasis]
      · intro b _ hba
        simp [pairBasis, hba]
      · simp
    simp [mixedPair, hadd, pairAnnihilate_smul, hb, map_ofNat, sub_eq_add_neg]
  rw [ha]
  ext A
  fin_cases A <;>
    norm_num [pairMode, pair01, pair23, annihilateMode, annihilation,
      Module.End.mul_apply, transition_apply, ket, OAI.LaughlinGap.Occupation.flip,
      sign, Finset.filter_insert, Finset.filter_singleton,
      Finset.ext_iff, Fin.forall_fin_succ, Finset.filter, Finset.card]

/-- A nonidentity one-particle contraction for an exact loss-rotation regression. -/
def scalarFilter : ℂ →L[ℂ] ℂ := (3 / 5 : ℂ) • 1

theorem scalarFilter_nonneg : 0 ≤ scalarFilter := by
  unfold scalarFilter
  exact smul_nonneg (by norm_num [Complex.le_def] : (0 : ℂ) ≤ 3 / 5)
    (show (0 : ℂ →L[ℂ] ℂ) ≤ 1 from zero_le_one)

theorem scalarFilter_contraction : ‖scalarFilter‖ ≤ 1 := by
  norm_num [scalarFilter, norm_smul]

theorem scalarFilter_defect : lossDefect scalarFilter = (4 / 5 : ℂ) • 1 := by
  unfold lossDefect
  apply CFC.sqrt_unique
  · ext
    simp [scalarFilter, pow_two, smul_eq_mul]
    ring
  · exact smul_nonneg (by norm_num [Complex.le_def] : (0 : ℂ) ≤ 4 / 5) zero_le_one

theorem scalarLoss_complex_input :
    lossRotation scalarFilter scalarFilter_nonneg scalarFilter_contraction
      (WithLp.toLp 2 (Complex.I, (0 : ℂ))) =
      WithLp.toLp 2 ((4 / 5 : ℂ) * Complex.I, (3 / 5 : ℂ) * Complex.I) := by
  rw [lossRotation_first_axis]
  change WithLp.toLp 2 (lossDefect scalarFilter Complex.I, scalarFilter Complex.I) = _
  rw [scalarFilter_defect]
  rfl

end VortexGap.Examples
