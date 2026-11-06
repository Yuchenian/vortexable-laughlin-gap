import VortexGap.Physical.OrbitalColumnCriterion
import VortexGap.Examples.CoordinateBand
import VortexGap.Physical.PlaneGramDomain

noncomputable section

namespace VortexGap.Fermion
open MeasureTheory
open scoped BoundedContinuousFunction
local notation "H" => Lp ℂ 2 (volume : Measure ℂ)
variable {ι : Type*} [Fintype ι] [Nonempty ι]
local notation "V" => EuclideanSpace ℂ ι

theorem coordinateBand_maximal_vortexability (F : ℂ ≃ₜ ℂ) (hf : ContDiff ℝ 2 F)
    (hJ : ∀ z, 0 < coordinateJacobian F z) (ell : ℝ) (hell : 0 < ell) (v : CountableOrbital)
    (y : H) (hy : ∀ᵐ z ∂volume, y z = F z * coordinateBandEmbedding F hf hJ ell hell v z) :
    ∃ w, coordinateBandEmbedding F hf hJ ell hell w = y := by
  obtain ⟨u,rfl⟩ := (coordinateUnitary F hf hJ).surjective y
  have hg := (coordinateUnitary_graph F hf hJ (planeLLLEmbedding ell hell v) u).mp hy
  obtain ⟨w,rfl⟩ := planeLLL_coordinate_range ell hell v (y := u) hg
  exact ⟨w,rfl⟩

theorem columnPlane_maximal_domain (ell : ℝ) (hell : 0 < ell) (t : ℂ →ᵇ V)
    (hG : IsStrictlyPositive (gramOperator (columnPlaneEmbedding ell hell t))) (v : CountableOrbital) :
    MemLp (fun z : ℂ => z • columnPlaneEmbedding ell hell t v z) 2 volume ↔
      planeLLLEmbedding ell hell v ∈ planeCoordinateDomain := by
  have hscalar : IsStrictlyPositive (planeScalarGram ell hell (columnEnvelope t)) := columnPlaneEmbedding_gram ell hell t ▸ hG
  rw [← planeBand_maximal_domain ell hell (columnEnvelope t) hscalar v, planeCoordinateDomain_iff]
  have hn : ∀ᵐ z ∂volume, ‖z • columnPlaneEmbedding ell hell t v z‖ =
      ‖z * planeScalarEmbedding ell hell (columnEnvelope t) v z‖ := by
    filter_upwards [columnPlaneEmbedding_coe ell hell t v,planeScalarEmbedding_coe ell hell (columnEnvelope t) v]
      with z hz hs
    rw [hz,hs,norm_smul,norm_smul,norm_mul,norm_mul]
    change _ = ‖z‖*(‖((‖t z‖ : ℝ):ℂ)‖*_)
    simp [mul_comm]
  constructor
  · intro hm
    exact hm.congr_norm (continuous_id.aestronglyMeasurable.mul (Lp.aestronglyMeasurable _)) hn
  · intro hm
    exact hm.congr_norm (continuous_id.aestronglyMeasurable.smul (Lp.aestronglyMeasurable _)) (hn.mono fun _ h => h.symm)

theorem columnPlane_maximal_vortexability (ell : ℝ) (hell : 0 < ell) (t : ℂ →ᵇ V)
    (hG : IsStrictlyPositive (gramOperator (columnPlaneEmbedding ell hell t))) (v : CountableOrbital)
    (y : Lp V 2 (volume : Measure ℂ)) (hy : ∀ᵐ z ∂volume, y z = z • columnPlaneEmbedding ell hell t v z) :
    ∃ w, columnPlaneEmbedding ell hell t w = y := by
  have hdom := (columnPlane_maximal_domain ell hell t hG v).mp ((Lp.memLp y).ae_eq hy)
  obtain ⟨w,hw⟩ := planeLLL_coordinate_range ell hell v (planeCoordinateMul_coe ⟨_,hdom⟩)
  refine ⟨w,Lp.ext ?_⟩
  have hcoord := planeCoordinateMul_coe ⟨_,hdom⟩
  change planeLLLEmbedding ell hell w = planeCoordinateMul ⟨planeLLLEmbedding ell hell v,hdom⟩ at hw
  rw [← hw] at hcoord
  filter_upwards [hy,columnPlaneEmbedding_coe ell hell t w,columnPlaneEmbedding_coe ell hell t v,
    planeLLLEmbedding_coe ell hell w,planeLLLEmbedding_coe ell hell v,hcoord] with z h hz hv h1 h2 h3
  rw [h1,h2] at h3
  rw [h,hz,hv,smul_smul,h3]

end VortexGap.Fermion
