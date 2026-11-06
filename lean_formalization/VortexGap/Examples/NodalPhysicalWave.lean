import VortexGap.Physical.PlaneBandConfigurationL2
import VortexGap.Examples.PlaneNodalFourier

noncomputable section
namespace VortexGap.Fermion
open MeasureTheory
open scoped ComplexOrder BoundedContinuousFunction
theorem planeNodal_zero_L2_image (ell : ℝ) (hell : 0<ell) (N : ℕ) (ψ : Lp ℂ 2 (planeConfigMeasure N)) :
    (∃ x : countableSector N, planeBandContactOperator ell hell (planeNodal ell) (planeNodal_gram_strict ell hell)
        (planeNodal_differentiable ell) N x = 0 ∧
      ψ = planeBandConfigurationL2 ell hell (planeNodal ell) (planeNodal_gram_strict ell hell) N x) ↔
    ∃ y : countableSector N, countablePairLift N planePairOperator y = 0 ∧
      ψ =ᵐ[planeConfigMeasure N] fun z => (∏ i, planeNodal ell (z i)) * planeReferenceConfigurationL2 ell hell N y z :=
  planeBand_zero_L2_image ell hell (planeNodal ell) (planeNodal_gram_strict ell hell)
    (planeNodal_differentiable ell) 1.98156 (by norm_num) (planeNodal_pair_lower ell hell) N ψ

/-- A node forces a zero of every band configuration representative at that coordinate. -/
theorem planeBand_wave_at_node (ell : ℝ) (hell : 0<ell) (f : ℂ →ᵇ ℂ)
    (hG : IsStrictlyPositive (planeScalarGram ell hell f)) {N : ℕ} (x : countableSector N)
    (z : Fin N → ℂ) (i : Fin N) (hi : f (z i) = 0) :
    planeConfigurationAmplitude (planeBandField ell hell f hG) x z = 0 := by
  let F := planeScalarEmbedding ell hell f
  let y := countableExteriorFilter N (gramInvSqrt F) (gramInvSqrt_nonneg F hG) x
  have he : countableExteriorFilter N (gramRoot F) (gramRoot_nonneg F) y = x :=
    Subtype.ext (countableDegreeFilter_cancel N (gramRoot F) (gramInvSqrt F) (gramRoot_nonneg F) (gramInvSqrt_nonneg F hG) (gramInvSqrt_right F hG) x)
  rw [← he,planeBand_configuration_product,Finset.prod_eq_zero (Finset.mem_univ i) hi,zero_mul]

theorem planeNodal_zero_at_node (ell : ℝ) (hell : 0<ell) {N : ℕ} (x : countableSector N)
    (z : Fin N → ℂ) (i : Fin N) (hi : z i = ((Real.pi/(2*planeNodalWaveNumber ell) : ℝ) : ℂ)) :
    planeConfigurationAmplitude (planeBandField ell hell (planeNodal ell) (planeNodal_gram_strict ell hell)) x z = 0 :=
  planeBand_wave_at_node ell hell _ _ x z i (hi ▸ planeNodal_has_zero ell hell)

end VortexGap.Fermion
end
