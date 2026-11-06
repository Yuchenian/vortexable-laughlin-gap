import VortexGap.Geometry.SphereRotatedContact
import VortexGap.Transfer.ContinuousFrame
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open VortexGap.Frame MeasureTheory OAI.Laughlin.Rotation
open scoped InnerProduct ENNReal ComplexOrder Matrix

/-- At flux n+1 the normalized pair measure has mass 2n+1. -/
def spherePairMeasure (n : ℕ) : Measure SourceSU2 := ENNReal.ofReal (2*(n:ℝ)+1) • sourceHaar

instance (n : ℕ) : IsFiniteMeasure (spherePairMeasure n) := by
  constructor
  simp [spherePairMeasure,Measure.smul_apply]

theorem sphereFrameColumn_continuous (n : ℕ) (j : Fin 2) :
    Continuous (fun g => sphereSpinFrame n g (PiLp.single 2 j 1)) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin (n+2) => ℂ)).comp
  apply continuous_pi
  intro i
  change Continuous (fun g => ((sphereSpinColumns n g) *ᵥ (Pi.single j (1:ℂ))) i)
  simpa [Matrix.mulVec,dotProduct,Pi.single_apply,sphereSpinColumns] using
    sourceSpinRepresentation_continuous (n+1) i (Fin.castLE (by omega) j)

private theorem row_continuous (n : ℕ) (g : SourceSU2) : Continuous (fun h =>
    traceNormTwo (twoFrameOverlap (sphereSpinFrame n g) (sphereSpinFrame n h))) := by
  cases n with
  | zero => simp_rw [sphereSpinFrame_flux_one_traceNorm]; exact continuous_const
  | succ n =>
    simp_rw [sphereSpinFrame_traceNorm]
    fun_prop

theorem spherePairMeasure_row (n : ℕ) (g : SourceSU2) :
    (∫ h, traceNormTwo (twoFrameOverlap (sphereSpinFrame n g) (sphereSpinFrame n h)) ∂spherePairMeasure n) =
      sphereRadialSchur n := by
  rw [spherePairMeasure,integral_smul_measure]
  simpa [ENNReal.toReal_ofReal (by positivity : 0 ≤ 2*(n:ℝ)+1)] using sphereSpinFrame_schur_row n g

theorem spherePairMeasure_operator (n : ℕ) :
    continuousPairOperator (spherePairMeasure n) (sphereOrbitPair n) = (spherePairSector n).starProjection := by
  have hs := spherePair_projector n
  unfold continuousPairOperator spherePairMeasure
  rw [integral_smul_measure]
  change _ • continuousPairOperator sourceHaar (sphereOrbitPair n) = _
  rw [← hs,RCLike.real_smul_eq_coe_smul (K := ℂ)]
  congr 1
  simp [ENNReal.toReal_ofReal (by positivity : 0 ≤ 2*(n:ℝ)+1)]

/-- Reference H is the CAR lift of the highest pair-spin projector in pair-projector units. -/
theorem spherePairMeasure_reference (n : ℕ) :
    continuousFrameHamiltonian (spherePairMeasure n) (sphereOrbitPair n) =
      LinearMap.toContinuousLinearMap (pairLift (spherePairSector n).starProjection.toLinearMap) := by
  rw [continuousFrameHamiltonian_pairLift _ _ ((sphereOrbitPair_continuous n).memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)),spherePairMeasure_operator]
  rfl

theorem sphereFiltered_transfer (n N : ℕ)
    (M : EuclideanSpace ℂ (Fin (n+2)) →L[ℂ] EuclideanSpace ℂ (Fin (n+2))) (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1)
    (γ : ℝ) (hgap : ∀ K ≤ N, ∀ y : Space (n+2), InSector K y →
      let H := pairLift (spherePairSector n).starProjection.toLinearMap
      γ*(inner ℂ y (H y)).re ≤ (inner ℂ y ((H*H) y)).re) {x : Space (n+2)} (hx : InSector N x) :
    let H := continuousFrameHamiltonian (spherePairMeasure n)
      (fun g => exteriorSquare M.toLinearMap (sphereOrbitPair n g))
    (γ-sphereRadialSchur n*‖1-M^2‖-‖1-M^2‖^2)*(inner ℂ x (H x)).re ≤ (inner ℂ x ((H*H) x)).re := by
  have hr := continuous_frame_transfer M hM hc (spherePairMeasure n) (sphereSpinFrame n)
    (sphereFrameColumn_continuous n 0).aestronglyMeasurable (sphereFrameColumn_continuous n 1).aestronglyMeasurable
    (fun _ => 1) (fun _ => zero_lt_one) aestronglyMeasurable_const (sphereRadialSchur n)
    (Filter.Eventually.of_forall fun g => by
      simp only [mul_one]
      exact (row_continuous n g).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (Filter.Eventually.of_forall fun g => by simpa only [mul_one] using (spherePairMeasure_row n g).le)
    1 (by norm_num) (fun q => by
      change (inner ℂ q (continuousPairOperator (spherePairMeasure n) (sphereOrbitPair n) q)).re ≤ _
      rw [spherePairMeasure_operator,one_mul,pow_two]
      exact (re_inner_le_norm (𝕜 := ℂ) _ _).trans (mul_le_mul_of_nonneg_left
        ((spherePairSector n).norm_starProjection_apply_le q) (norm_nonneg _)))
    γ (fun K hK y hy => by
      let T := continuousFrameHamiltonian (spherePairMeasure n) (sphereOrbitPair n)
      change γ*(inner ℂ y (T y)).re ≤ (inner ℂ y ((T*T) y)).re
      dsimp only [T]
      rw [spherePairMeasure_reference]
      exact hgap K hK y hy) hx
  simpa only [sphereOrbitPair,one_mul] using! hr

end VortexGap.Fermion
