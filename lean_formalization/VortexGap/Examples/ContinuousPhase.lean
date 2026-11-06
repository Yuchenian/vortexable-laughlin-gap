import VortexGap.Frame.ContinuousPairLift
import VortexGap.Examples.WeightedLoss
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

noncomputable section
set_option autoImplicit false
namespace VortexGap.Examples
open VortexGap.Fermion MeasureTheory OAI.LaughlinGap.Occupation
open scoped InnerProduct ComplexConjugate ENNReal

/-- Lebesgue labels on an interval of mass one; no label delta vectors. -/
def phaseMeasure : Measure ℝ := volume.restrict (Set.Icc 0 1)

instance : IsFiniteMeasure phaseMeasure := by
  unfold phaseMeasure
  infer_instance

def phaseScalar (t : ℝ) : ℂ := Complex.exp ((Real.pi * t : ℝ) * Complex.I)
def phasePair (t : ℝ) : PairSpace 2 := phaseScalar t • weightedUnitPair

theorem phaseMeasure_mass : phaseMeasure.real Set.univ = 1 := by
  simp [phaseMeasure, measureReal_def, Real.volume_Icc]

theorem phaseScalar_norm (t : ℝ) : ‖phaseScalar t‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I _

theorem phaseScalar_endpoints : phaseScalar 0 = 1 ∧ phaseScalar 1 = -1 := by
  simp [phaseScalar, Complex.exp_pi_mul_I]

theorem phasePair_continuous : Continuous phasePair := by
  unfold phasePair phaseScalar
  fun_prop

theorem phasePair_norm (t : ℝ) : ‖phasePair t‖ = 1 := by
  rw [phasePair, norm_smul, phaseScalar_norm, weightedUnitPair_norm, one_mul]

theorem phasePair_memLp : MemLp phasePair 2 phaseMeasure :=
  MemLp.of_bound phasePair_continuous.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun t => (phasePair_norm t).le)

theorem phasePair_rankOne (t : ℝ) :
    InnerProductSpace.rankOne ℂ (phasePair t) (phasePair t) =
      InnerProductSpace.rankOne ℂ weightedUnitPair weightedUnitPair := by
  apply ContinuousLinearMap.ext
  intro q
  change (inner ℂ (phaseScalar t • weightedUnitPair) q) •
    (phaseScalar t • weightedUnitPair) = (inner ℂ weightedUnitPair q) • weightedUnitPair
  rw [inner_smul_left, smul_smul]
  have hc : conj (phaseScalar t) * phaseScalar t = 1 := by
    rw [Complex.conj_mul', phaseScalar_norm]
    norm_num
  congr 1
  calc
    _ = (conj (phaseScalar t) * phaseScalar t) * inner ℂ weightedUnitPair q := by ring
    _ = _ := by rw [hc, one_mul]

theorem phasePair_operator :
    continuousPairOperator phaseMeasure phasePair =
      InnerProductSpace.rankOne ℂ weightedUnitPair weightedUnitPair := by
  haveI : CompleteSpace (PairSpace 2) := PiLp.completeSpace 2 (fun _ => ℂ)
  haveI : CompleteSpace (PairSpace 2 →L[ℂ] PairSpace 2) := ContinuousLinearMap.instCompleteSpace
  simp_rw [continuousPairOperator, phasePair_rankOne]
  rw [integral_const, phaseMeasure_mass, one_smul]

theorem phasePair_annihilation (t : ℝ) :
    pairAnnihilate (phasePair t) (ket {0,1}) = conj (phaseScalar t) • ket ∅ := by
  rw [phasePair, pairAnnihilate_smul, LinearMap.smul_apply, ← weightedUnitPair_embed,
    pairAnnihilate_pairEmbed, inner_self_eq_norm_sq_to_K, weightedUnitPair_norm]
  simp

theorem phasePair_energy :
    (inner ℂ (ket {0,1}) (continuousFrameHamiltonian phaseMeasure phasePair (ket {0,1}))).re = 1 := by
  rw [continuousFrameHamiltonian_energy phaseMeasure phasePair phasePair_memLp]
  simp_rw [phasePair_annihilation, norm_smul, Complex.norm_conj, phaseScalar_norm, ket_norm]
  simp [integral_const, phaseMeasure_mass]

/-- A real nonidentity filter in the same continuous-label test. -/
def phaseFilteredPair (t : ℝ) : PairSpace 2 := exteriorSquare lossFilter.toLinearMap (phasePair t)

theorem phaseFilteredPair_memLp : MemLp phaseFilteredPair 2 phaseMeasure := by
  have hc : Continuous phaseFilteredPair :=
    (LinearMap.toContinuousLinearMap (exteriorSquare lossFilter.toLinearMap)).continuous.comp phasePair_continuous
  apply MemLp.of_bound hc.aestronglyMeasurable ‖exteriorSquare lossFilter.toLinearMap weightedUnitPair‖
  exact Filter.Eventually.of_forall fun t => by
    simp only [phaseFilteredPair, phasePair, map_smul, norm_smul, phaseScalar_norm, one_mul, le_refl]

theorem phaseFilteredPair_energy :
    (inner ℂ (ket {0,1})
      (continuousFrameHamiltonian phaseMeasure phaseFilteredPair (ket {0,1}))).re = 81/625 := by
  rw [continuousFrameHamiltonian_energy phaseMeasure phaseFilteredPair phaseFilteredPair_memLp]
  have heq : (fun t => ‖pairAnnihilate (phaseFilteredPair t) (ket {0,1})‖^2) =
      fun _ : ℝ => (81/625 : ℝ) := by
    funext t
    rw [phaseFilteredPair, phasePair, map_smul, pairAnnihilate_smul,
      LinearMap.smul_apply, weighted_filtered_pair_base]
    norm_num [norm_smul, Complex.norm_conj, phaseScalar_norm, ket_norm]
  rw [heq, integral_const, phaseMeasure_mass, one_smul]

end VortexGap.Examples
