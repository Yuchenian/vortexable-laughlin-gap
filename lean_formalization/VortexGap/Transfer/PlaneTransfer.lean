import VortexGap.Geometry.PlaneSchur
import VortexGap.Geometry.PlaneMeasurability
import VortexGap.Geometry.PlaneResolution
import VortexGap.Transfer.CountableContinuousSpectrum
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory VortexGap.Frame
open scoped ComplexOrder

def planeFilteredHamiltonian (M : CountableOrbital →L[ℂ] CountableOrbital)
    (hM : 0 ≤ M) (N : ℕ) : countableSector N →L[ℂ] countableSector N :=
  countableContinuousFilteredHamiltonian planePairMeasure
    (fun z => countableTwoFramePair (planeTwoFrame z)) planePair_coefficient_memLp
    1 (by norm_num) (fun q => by simpa only [one_mul] using planePair_bessel q) M hM N

/-- All plane geometry inputs are proved. The only gap input is in the original
reference sectors k<=N; the concrete CAR theorem derives loss noise and dilation. -/
theorem plane_filtered_transfer
    (M : CountableOrbital →L[ℂ] CountableOrbital) (hM : 0 ≤ M) (hMc : ‖M‖ ≤ 1)
    (γ : ℝ) (N : ℕ)
    (hgap : ∀ k ≤ N, (countablePairLift k planePairOperator * countablePairLift k planePairOperator -
      (γ : ℂ) • countablePairLift k planePairOperator).IsPositive) :
    let H := planeFilteredHamiltonian M hM N
    (H*H - ((γ-14*‖1-M^2‖-‖1-M^2‖^2 : ℝ) : ℂ) • H).IsPositive := by
  have h := countable_continuous_frame_transfer planePairMeasure planeTwoFrame
    planeTwoFrame_first_aestronglyMeasurable planeTwoFrame_second_aestronglyMeasurable
    planePair_coefficient_memLp 1 (by norm_num)
    (fun q => by simpa only [one_mul] using planePair_bessel q)
    M hM hMc (fun _ => 1) (fun _ => by norm_num) aestronglyMeasurable_const 14
    (Filter.Eventually.of_forall (fun z => by simpa only [mul_one] using planeTwoFrame_schur_integrable z))
    (Filter.Eventually.of_forall (fun z => by simpa only [mul_one] using planeTwoFrame_schur_fourteen z))
    γ N hgap
  simpa only [one_mul, planeFilteredHamiltonian] using h

theorem planeFilteredHamiltonian_positive
    (M : CountableOrbital →L[ℂ] CountableOrbital) (hM : 0 ≤ M) (hMc : ‖M‖ ≤ 1) (N : ℕ) :
    (planeFilteredHamiltonian M hM N).IsPositive :=
  countableContinuousFilteredHamiltonian_positive _ _ _ _ _ _ M hM hMc N

theorem plane_filtered_spectrum_gap
    (M : CountableOrbital →L[ℂ] CountableOrbital) (hM : 0 ≤ M) (hMc : ‖M‖ ≤ 1)
    (γ : ℝ) (N : ℕ)
    (hgap : ∀ k ≤ N, (countablePairLift k planePairOperator * countablePairLift k planePairOperator -
      (γ : ℂ) • countablePairLift k planePairOperator).IsPositive) :
    Disjoint (spectrum ℝ (planeFilteredHamiltonian M hM N))
      (Set.Ioo 0 (γ-14*‖1-M^2‖-‖1-M^2‖^2)) :=
  VortexGap.quadratic_gap_spectrum_excludes _ (planeFilteredHamiltonian_positive M hM hMc N) _
    (plane_filtered_transfer M hM hMc γ N hgap)

end VortexGap.Fermion
