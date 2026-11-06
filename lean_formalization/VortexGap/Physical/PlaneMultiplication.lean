import VortexGap.Geometry.PlanePhysicalL2
import VortexGap.Physical.GramOrthogonalization
import Mathlib.Topology.ContinuousMap.Bounded.Normed
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory
open scoped BoundedContinuousFunction

theorem planeScalar_coefficient_memLp (ell : ℝ) (hell : 0 < ell) (f : ℂ →ᵇ ℂ) (v : CountableOrbital) :
    MemLp (fun z => f z * inner ℂ (planeEvaluation ell z) v) 2 volume := by
  apply (planeEvaluation_coefficient_memLp ell hell v).of_le_mul (c := ‖f‖)
    (f.continuous.mul ((planeEvaluation_continuous ell).inner continuous_const)).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun z => by
    change ‖f z * inner ℂ (planeEvaluation ell z) v‖ ≤ ‖f‖ * ‖inner ℂ (planeEvaluation ell z) v‖
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (f.norm_coe_le_norm z) (norm_nonneg _))

theorem planeScalar_coefficient_bound (ell : ℝ) (hell : 0 < ell) (f : ℂ →ᵇ ℂ) (v : CountableOrbital) :
    (∫ z : ℂ, ‖f z * inner ℂ (planeEvaluation ell z) v‖^2) ≤ ‖f‖^2*‖v‖^2 := by
  have hi := (memLp_two_iff_integrable_sq_norm
    (planeScalar_coefficient_memLp ell hell f v).aestronglyMeasurable).mp
      (planeScalar_coefficient_memLp ell hell f v)
  have hj := (memLp_two_iff_integrable_sq_norm
    (planeEvaluation_coefficient_memLp ell hell v).aestronglyMeasurable).mp
      (planeEvaluation_coefficient_memLp ell hell v)
  rw [← planeEvaluation_integral_norm_sq ell hell v, ← integral_const_mul]
  apply integral_mono hi (hj.const_mul (‖f‖^2))
  intro z
  change ‖f z * inner ℂ (planeEvaluation ell z) v‖^2 ≤ ‖f‖^2 * ‖inner ℂ (planeEvaluation ell z) v‖^2
  rw [norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (norm_nonneg _) (f.norm_coe_le_norm z) 2) (sq_nonneg _)

/-- Actual multiplication of each physical LLL wavefunction by the bounded scalar f. -/
def planeScalarEmbedding (ell : ℝ) (hell : 0 < ell) (f : ℂ →ᵇ ℂ) :
    CountableOrbital →L[ℂ] Lp ℂ 2 (volume : Measure ℂ) :=
  Frame.besselAnalysis volume (fun z => f z • innerSL ℂ (planeEvaluation ell z))
    (planeScalar_coefficient_memLp ell hell f) (‖f‖^2) (sq_nonneg _) (planeScalar_coefficient_bound ell hell f)

theorem planeScalarEmbedding_coe (ell : ℝ) (hell : 0 < ell) (f : ℂ →ᵇ ℂ) (v : CountableOrbital) :
    planeScalarEmbedding ell hell f v =ᵐ[volume] (fun z => f z * inner ℂ (planeEvaluation ell z) v) :=
  Frame.besselAnalysis_ae _ _ _ _ _ _ v

theorem planeScalarEmbedding_is_multiplication (ell : ℝ) (hell : 0 < ell) (f : ℂ →ᵇ ℂ)
    (v : CountableOrbital) :
    planeScalarEmbedding ell hell f v =ᵐ[volume] (fun z => f z * planeLLLEmbedding ell hell v z) := by
  filter_upwards [planeScalarEmbedding_coe ell hell f v, planeLLLEmbedding_coe ell hell v] with z hf hv
  rw [hf, hv]

def planeScalarGram (ell : ℝ) (hell : 0 < ell) (f : ℂ →ᵇ ℂ) : CountableOrbital →L[ℂ] CountableOrbital :=
  gramOperator (planeScalarEmbedding ell hell f)

theorem planeScalarGram_energy (ell : ℝ) (hell : 0 < ell) (f : ℂ →ᵇ ℂ) (v : CountableOrbital) :
    (inner ℂ v (planeScalarGram ell hell f v)).re =
      ∫ z : ℂ, ‖f z‖^2 * ‖inner ℂ (planeEvaluation ell z) v‖^2 := by
  change (inner ℂ v ((planeScalarEmbedding ell hell f).adjoint (planeScalarEmbedding ell hell f v))).re = _
  rw [ContinuousLinearMap.adjoint_inner_right, ← RCLike.re_eq_complex_re,
    ← norm_sq_eq_re_inner (𝕜 := ℂ)]
  have h := Frame.besselAnalysis_norm_sq volume (fun z => f z • innerSL ℂ (planeEvaluation ell z))
    (planeScalar_coefficient_memLp ell hell f) (‖f‖^2) (sq_nonneg _)
    (planeScalar_coefficient_bound ell hell f) v
  change ‖planeScalarEmbedding ell hell f v‖^2 = ∫ z, ‖f z * inner ℂ (planeEvaluation ell z) v‖^2 at h
  simpa only [norm_mul, mul_pow] using h

theorem planeScalarEmbedding_range_closed (ell : ℝ) (hell : 0 < ell) (f : ℂ →ᵇ ℂ)
    (hG : IsStrictlyPositive (planeScalarGram ell hell f)) :
    IsClosed ((planeScalarEmbedding ell hell f).toLinearMap.range : Set (Lp ℂ 2 (volume : Measure ℂ))) :=
  gramRange_closed _ hG

/-- Gram orthogonalization onto the actual multiplied LLL range. -/
def planeScalarUnitary (ell : ℝ) (hell : 0 < ell) (f : ℂ →ᵇ ℂ)
    (hG : IsStrictlyPositive (planeScalarGram ell hell f)) :
    CountableOrbital ≃ₗᵢ[ℂ] (planeScalarEmbedding ell hell f).toLinearMap.range :=
  gramRangeUnitary _ hG

theorem planeScalarUnitary_coe (ell : ℝ) (hell : 0 < ell) (f : ℂ →ᵇ ℂ)
    (hG : IsStrictlyPositive (planeScalarGram ell hell f)) (v : CountableOrbital) :
    (planeScalarUnitary ell hell f hG v : Lp ℂ 2 (volume : Measure ℂ)) =ᵐ[volume]
      (fun z => f z * inner ℂ (planeEvaluation ell z)
        (gramInvSqrt (planeScalarEmbedding ell hell f) v)) :=
  planeScalarEmbedding_coe ell hell f _

theorem planeScalarEmbedding_one (ell : ℝ) (hell : 0 < ell) :
    planeScalarEmbedding ell hell (1 : ℂ →ᵇ ℂ) = (planeLLLEmbedding ell hell).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro v
  apply Lp.ext
  filter_upwards [planeScalarEmbedding_coe ell hell 1 v, planeLLLEmbedding_coe ell hell v] with z hf hv
  rw [hf]
  change (1 : ℂ →ᵇ ℂ) z * inner ℂ (planeEvaluation ell z) v = planeLLLEmbedding ell hell v z
  rw [hv]
  simp

end VortexGap.Fermion





