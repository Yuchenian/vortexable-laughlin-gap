import VortexGap.Frame.L2CutoffLimits
import VortexGap.Examples.CountableOrbitals
import VortexGap.Operator.L2Exchange
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
noncomputable section
set_option autoImplicit false
namespace VortexGap.Examples
open MeasureTheory VortexGap.Frame VortexGap.Fermion
open scoped InnerProduct ENNReal Topology

def countableCoordinateField (j : ℕ) : CountableOrbital →L[ℂ] ℂ :=
  lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 j

theorem countableCoordinate_memLp (x : CountableOrbital) :
    MemLp (fun j => countableCoordinateField j x) 2 (Measure.count : Measure ℕ) := by
  change MemLp (fun j => x j) 2 (Measure.count : Measure ℕ)
  apply (memLp_two_iff_integrable_sq_norm
    (continuous_of_discreteTopology : Continuous (fun j : ℕ => x j)).aestronglyMeasurable).mpr
  apply integrable_count_iff.mpr
  simpa only [Real.norm_eq_abs, abs_sq, abs_norm] using VortexGap.l2_norm_sq_summable x

theorem countableCoordinate_energy (x : CountableOrbital) :
    (∫ j, ‖countableCoordinateField j x‖^2 ∂(Measure.count : Measure ℕ)) = ‖x‖^2 := by
  have hi := (memLp_two_iff_integrable_sq_norm
    (countableCoordinate_memLp x).aestronglyMeasurable).mp (countableCoordinate_memLp x)
  rw [integral_countable hi]
  simp only [count_real_singleton, one_smul]
  exact (VortexGap.l2_norm_sq x).symm

def countableCoordinateAnalysis : CountableOrbital →L[ℂ] Lp ℂ 2 (Measure.count : Measure ℕ) :=
  besselAnalysis Measure.count countableCoordinateField countableCoordinate_memLp
    1 (by norm_num) (fun x => by rw [countableCoordinate_energy]; simp)

theorem countableCoordinateAnalysis_ae (x : CountableOrbital) :
    countableCoordinateAnalysis x =ᵐ[Measure.count] fun j => x j :=
  besselAnalysis_ae _ _ _ _ _ _ x

theorem countableCoordinateAnalysis_norm (x : CountableOrbital) :
    ‖countableCoordinateAnalysis x‖ = ‖x‖ := by
  have h : ‖countableCoordinateAnalysis x‖^2 = ‖x‖^2 := by
    rw [countableCoordinateAnalysis, besselAnalysis_norm_sq, countableCoordinate_energy]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

theorem countableLabel_measure_infinite :
    (Measure.count : Measure ℕ) Set.univ = ∞ :=
  Measure.count_apply_infinite Set.infinite_univ

theorem countableCoordinateField_norm (j : ℕ) : ‖countableCoordinateField j‖ = 1 := by
  have h : countableCoordinateField j = innerSL ℂ (orbitalKet j) := by
    apply ContinuousLinearMap.ext
    intro x
    exact (orbitalKet_inner_left j x).symm
  rw [h, innerSL_apply_norm, orbitalKet_norm]

/-- This field fails the old global operator-norm L2 envelope, while its analysis is an isometry. -/
theorem countableCoordinateField_not_memLp :
    ¬ MemLp countableCoordinateField 2 (Measure.count : Measure ℕ) := by
  intro h
  have hn : MemLp (fun _ : ℕ => (1 : ℝ)) 2 Measure.count := by
    simpa only [countableCoordinateField_norm] using h.norm
  have he := (memLp_const_iff (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞)).mp hn
  simpa only [countableLabel_measure_infinite, lt_self_iff_false, or_false, one_ne_zero] using he

theorem countableCoordinate_geometric_norm_sq :
    ‖countableCoordinateAnalysis geometricOrbital‖^2 = (4/3 : ℝ) := by
  rw [countableCoordinateAnalysis_norm, geometricOrbital_norm_sq]

theorem countableCoordinate_geometric_ae :
    countableCoordinateAnalysis geometricOrbital =ᵐ[Measure.count]
      fun j => (Complex.I/2 : ℂ)^j :=
  countableCoordinateAnalysis_ae geometricOrbital

theorem countableCoordinate_geometric_cutoff :
    Filter.Tendsto (fun n => l2Cutoff Measure.count
      (spanningSets (Measure.count : Measure ℕ) n)
      (measurableSet_spanningSets Measure.count n) (countableCoordinateAnalysis geometricOrbital))
      Filter.atTop (𝓝 (countableCoordinateAnalysis geometricOrbital)) :=
  l2Cutoff_spanning_tendsto _ _
end VortexGap.Examples
