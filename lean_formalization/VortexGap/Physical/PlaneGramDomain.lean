import VortexGap.Physical.ClosedGraphNeumann
import Mathlib.Topology.ContinuousMap.Bounded.Star
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory Filter
open scoped InnerProduct ComplexOrder BoundedContinuousFunction
local notation "H" => Lp ℂ 2 (volume : Measure ℂ)

private theorem scalar_as_ambient (ell : ℝ) (hell : 0 < ell) (f : ℂ →ᵇ ℂ) (v : CountableOrbital) :
    planeScalarEmbedding ell hell f v = planeAmbientMultiply f (planeLLLEmbedding ell hell v) :=
  Lp.ext ((planeScalarEmbedding_is_multiplication ell hell f v).trans (planeAmbientMultiply_coe _ _).symm)

private theorem weight_as_ambient (ell : ℝ) (hell : 0 < ell) (f : ℂ →ᵇ ℂ) (v : CountableOrbital) :
    planeScalarEmbedding ell hell (star f * f) v = planeAmbientMultiply (star f) (planeScalarEmbedding ell hell f v) := by
  apply Lp.ext
  filter_upwards [planeScalarEmbedding_is_multiplication ell hell (star f * f) v,
    planeScalarEmbedding_is_multiplication ell hell f v,
    planeAmbientMultiply_coe (star f) (planeScalarEmbedding ell hell f v)] with z ht hf ha
  rw [ht,ha,hf]
  simp only [BoundedContinuousFunction.mul_apply]
  ring

theorem planeScalarGram_compression (ell : ℝ) (hell : 0 < ell) (f : ℂ →ᵇ ℂ) (v : CountableOrbital) :
    planeScalarGram ell hell f v = (planeLLLEmbedding ell hell).toContinuousLinearMap.adjoint
      (planeScalarEmbedding ell hell (star f * f) v) := by
  apply ext_inner_left ℂ
  intro u
  change inner ℂ u ((planeScalarEmbedding ell hell f).adjoint (planeScalarEmbedding ell hell f v)) = _
  rw [ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_right,
    MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [planeScalarEmbedding_is_multiplication ell hell f u,
    planeScalarEmbedding_is_multiplication ell hell f v,
    planeScalarEmbedding_is_multiplication ell hell (star f*f) v] with z hu hv hw
  rw [hu,hv,hw]
  simp only [RCLike.inner_apply', map_mul, BoundedContinuousFunction.mul_apply,
    BoundedContinuousFunction.star_apply, Complex.star_def, LinearIsometry.coe_toContinuousLinearMap]
  ring

/-- Recover graph-domain membership from membership of the compressed Gram image. -/
theorem planeGram_coordinate_preimage (ell : ℝ) (hell : 0 < ell) (f : ℂ →ᵇ ℂ)
    (hA : IsStrictlyPositive (planeScalarGram ell hell f)) (v : CountableOrbital)
    (hd : planeLLLEmbedding ell hell (planeScalarGram ell hell f v) ∈ planeCoordinateDomain) :
    planeLLLEmbedding ell hell v ∈ planeCoordinateDomain := by
  let J := (planeLLLEmbedding ell hell).toContinuousLinearMap
  let W := planeScalarEmbedding ell hell (star f*f)
  let A := planeScalarGram ell hell f
  let C := planeCoordinateCommutator ell hell
  let P := planeLLLProjection ell hell
  let B := J.adjoint.comp (C.comp W)
  let G := planeCoordinateGraph.comap (J.toLinearMap.prodMap J.toLinearMap)
  have hc : IsClosed (G : Set (CountableOrbital × CountableOrbital)) :=
    planeCoordinateGraph_closed.preimage ((J.continuous.comp continuous_fst).prodMk (J.continuous.comp continuous_snd))
  have hAeq (u : CountableOrbital) : A u = J.adjoint (W u) := planeScalarGram_compression ell hell f u
  have hproj (u : CountableOrbital) : P (W u) = J (A u) := congrArg J (hAeq u).symm
  have hstep (p : CountableOrbital × CountableOrbital) (hp : p ∈ G) :
      (A p.1, A p.2 + B p.1) ∈ G := by
    have hw := planeCoordinateGraph_multiply (star f*f) (J p.1) (J p.2) hp
    change (planeAmbientMultiply _ (planeLLLEmbedding ell hell p.1),
      planeAmbientMultiply _ (planeLLLEmbedding ell hell p.2)) ∈ _ at hw
    rw [← scalar_as_ambient, ← scalar_as_ambient] at hw
    have hg := planeLLLProjection_graph_map ell hell hw
    change (P (W p.1), P (W p.2) + C (W p.1)) ∈ planeCoordinateGraph at hg
    rw [hproj] at hg
    obtain ⟨u,hu⟩ := planeLLL_coordinate_range ell hell (A p.1) hg
    have hh := congrArg P hu
    change P (planeLLLEmbedding ell hell u) = _ at hh
    rw [planeLLLProjection_fixes, hu] at hh
    change (J (A p.1), J (A p.2 + B p.1)) ∈ planeCoordinateGraph
    rw [map_add]
    have hb : J (B p.1) = P (C (W p.1)) := rfl
    rw [hb, ← hproj p.2]
    have hf : P (P (W p.2)) = P (W p.2) := planeLLLProjection_fixes ell hell _
    rw [map_add, hf] at hh
    rwa [← hh]
  let x : planeCoordinateDomain := ⟨J (A v),hd⟩
  obtain ⟨b,hb⟩ := planeLLL_coordinate_range ell hell (A v) (planeCoordinateMul_coe x)
  have hg : (A v,b) ∈ G := by
    change (J (A v),planeLLLEmbedding ell hell b) ∈ planeCoordinateGraph
    rw [hb]
    exact planeCoordinateMul_coe x
  obtain ⟨y,hy⟩ := closedGraph_strictPositive_preimage G hc A B hA hstep v b hg
  exact ⟨(J v,J y),hy,rfl⟩

theorem planeGramInverse_preserves_domain (ell : ℝ) (hell : 0 < ell) (f : ℂ →ᵇ ℂ)
    (hA : IsStrictlyPositive (planeScalarGram ell hell f)) (v : CountableOrbital)
    (hv : planeLLLEmbedding ell hell v ∈ planeCoordinateDomain) :
    planeLLLEmbedding ell hell ((Ring.inverse (planeScalarGram ell hell f) :
      CountableOrbital →L[ℂ] CountableOrbital) v) ∈ planeCoordinateDomain := by
  apply planeGram_coordinate_preimage ell hell f hA
  have hi : planeScalarGram ell hell f ((Ring.inverse (planeScalarGram ell hell f) :
      CountableOrbital →L[ℂ] CountableOrbital) v) = v :=
    congrArg (fun T : CountableOrbital →L[ℂ] CountableOrbital => T v)
      (Ring.mul_inverse_cancel _ hA.isUnit)
  rwa [hi]

/-- Exact maximal domain without a pointwise lower bound on the multiplier. -/
theorem planeBand_maximal_domain (ell : ℝ) (hell : 0 < ell) (f : ℂ →ᵇ ℂ)
    (hA : IsStrictlyPositive (planeScalarGram ell hell f)) (v : CountableOrbital) :
    planeScalarEmbedding ell hell f v ∈ planeCoordinateDomain ↔
      planeLLLEmbedding ell hell v ∈ planeCoordinateDomain := by
  constructor
  · intro hv
    apply planeGram_coordinate_preimage ell hell f hA
    rw [planeScalarGram_compression]
    change planeLLLProjection ell hell (planeScalarEmbedding ell hell (star f*f) v) ∈ _
    apply planeLLLProjection_preserves_domain ell hell ⟨_,?_⟩
    rw [weight_as_ambient]
    exact planeCoordinateDomain_multiply (star f) ⟨_,hv⟩
  · intro hv
    rw [scalar_as_ambient]
    exact planeCoordinateDomain_multiply f ⟨_,hv⟩

theorem planeBand_maximal_vortexability (ell : ℝ) (hell : 0 < ell) (f : ℂ →ᵇ ℂ)
    (hA : IsStrictlyPositive (planeScalarGram ell hell f)) (v : CountableOrbital) {y : H}
    (hy : (planeScalarEmbedding ell hell f v,y) ∈ planeCoordinateGraph) :
    ∃ w, planeScalarEmbedding ell hell f w = y :=
  planeBand_coordinate_range_of_domain ell hell f v ((planeBand_maximal_domain ell hell f hA v).mp
    ((planeCoordinateGraph_iff _ _).mp hy).choose) hy

/-- Set equality in the ambient Lebesgue L2 space. -/
theorem planeBand_domain_intersection (ell : ℝ) (hell : 0 < ell) (f : ℂ →ᵇ ℂ)
    (hA : IsStrictlyPositive (planeScalarGram ell hell f)) :
    (Set.range (planeScalarEmbedding ell hell f) ∩ (planeCoordinateDomain : Set H)) =
      planeAmbientMultiply f '' (Set.range (planeLLLEmbedding ell hell) ∩ (planeCoordinateDomain : Set H)) := by
  ext x
  constructor
  · rintro ⟨⟨v,rfl⟩,hv⟩
    exact ⟨_, ⟨⟨v,rfl⟩,(planeBand_maximal_domain ell hell f hA v).mp hv⟩,
      (scalar_as_ambient ell hell f v).symm⟩
  · rintro ⟨_,⟨⟨v,rfl⟩,hv⟩,rfl⟩
    rw [← scalar_as_ambient]
    exact ⟨⟨v,rfl⟩,(planeBand_maximal_domain ell hell f hA v).mpr hv⟩

end VortexGap.Fermion
