import VortexGap.Physical.PlaneCoordinateSchur
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory Filter
open scoped BoundedContinuousFunction
local notation "H" => Lp ℂ 2 (volume : Measure ℂ)

private theorem graph_unique {x y v : H} (h : (x,y) ∈ planeCoordinateGraph)
    (g : (x,v) ∈ planeCoordinateGraph) : y = v :=
  Lp.ext ((show y =ᵐ[volume] fun z => z*x z from h).trans (Filter.EventuallyEq.symm g))

theorem planeLLLProjection_graph_map (ell : ℝ) (hell : 0 < ell) {x y : H}
    (h : (x,y) ∈ planeCoordinateGraph) :
    (planeLLLProjection ell hell x,
      planeLLLProjection ell hell y + planeCoordinateCommutator ell hell x) ∈ planeCoordinateGraph := by
  obtain ⟨hx,rfl⟩ := (planeCoordinateGraph_iff _ _).mp h
  exact planeLLLProjection_coordinateGraph ell hell ⟨x,hx⟩

theorem planeCoordinateCommutator_LLL (ell : ℝ) (hell : 0 < ell) (v : CountableOrbital) :
    planeCoordinateCommutator ell hell (planeLLLEmbedding ell hell v) = 0 := by
  let J := planeLLLEmbedding ell hell
  let P := planeLLLProjection ell hell
  let C := planeCoordinateCommutator ell hell
  have he : C.comp J.toContinuousLinearMap = 0 := by
    apply countableOrbital_clm_ext
    intro j
    let c : ℂ := ((Real.sqrt 2 * ell * Real.sqrt (j+1 : ℝ) : ℝ) : ℂ)
    have hg : (J (orbitalKet j), c • J (orbitalKet (j+1))) ∈ planeCoordinateGraph := by
      change ∀ᵐ z ∂volume, (c • J (orbitalKet (j+1))) z = z * J (orbitalKet j) z
      filter_upwards [Lp.coeFn_smul c (J (orbitalKet (j+1))), planeLLLEmbedding_basis ell hell j,
        planeLLLEmbedding_basis ell hell (j+1)] with z hc ha hb
      simp only [hc, Pi.smul_apply, smul_eq_mul, J, ha, hb, planeWavefunction_coordinate_raise ell hell]
      rfl
    have hp := planeLLLProjection_graph_map ell hell hg
    change (P (J (orbitalKet j)), P (c • J (orbitalKet (j+1))) + C (J (orbitalKet j))) ∈ _ at hp
    have hfix (u : CountableOrbital) : P (J u) = J u := planeLLLProjection_fixes ell hell u
    rw [map_smul, hfix, hfix] at hp
    have hh := graph_unique hp hg
    change C (J (orbitalKet j)) = 0
    exact add_eq_left.mp hh
  exact congrArg (fun T : CountableOrbital →L[ℂ] H => T v) he

/-- Every LLL state in the maximal ambient domain is taken back into the LLL. -/
theorem planeLLL_coordinate_range (ell : ℝ) (hell : 0 < ell) (v : CountableOrbital) {y : H}
    (h : (planeLLLEmbedding ell hell v,y) ∈ planeCoordinateGraph) :
    ∃ w, planeLLLEmbedding ell hell w = y := by
  have hp := planeLLLProjection_graph_map ell hell h
  rw [planeLLLProjection_fixes, planeCoordinateCommutator_LLL, add_zero] at hp
  exact ⟨(planeLLLEmbedding ell hell).toContinuousLinearMap.adjoint y, graph_unique hp h⟩

theorem planeBand_coordinate_range_of_domain (ell : ℝ) (hell : 0 < ell) (f : ℂ →ᵇ ℂ)
    (v : CountableOrbital) (hv : planeLLLEmbedding ell hell v ∈ planeCoordinateDomain) {y : H}
    (hy : (planeScalarEmbedding ell hell f v,y) ∈ planeCoordinateGraph) :
    ∃ w, planeScalarEmbedding ell hell f w = y := by
  let J := planeLLLEmbedding ell hell
  have he (u : CountableOrbital) : planeScalarEmbedding ell hell f u = planeAmbientMultiply f (J u) :=
    Lp.ext ((planeScalarEmbedding_is_multiplication ell hell f u).trans (planeAmbientMultiply_coe _ _).symm)
  let x : planeCoordinateDomain := ⟨J v,hv⟩
  obtain ⟨w,hw⟩ := planeLLL_coordinate_range ell hell v (planeCoordinateMul_coe x)
  have hg := planeCoordinateGraph_multiply f (J v) (planeCoordinateMul x) (planeCoordinateMul_coe x)
  rw [← he v] at hg
  exact ⟨w, (he w).trans ((congrArg (planeAmbientMultiply f) hw).trans (graph_unique hg hy))⟩

theorem planeWeakCos_maximal_vortexability (ell : ℝ) (hell : 0 < ell)
    (v : CountableOrbital) {y : H}
    (hy : (planeScalarEmbedding ell hell planeWeakCos v,y) ∈ planeCoordinateGraph) :
    ∃ w, planeScalarEmbedding ell hell planeWeakCos w = y :=
  planeBand_coordinate_range_of_domain ell hell planeWeakCos v ((planeWeakCos_coordinate_iff ell hell v).mp
    ((planeCoordinateGraph_iff _ _).mp hy).choose) hy

end VortexGap.Fermion
