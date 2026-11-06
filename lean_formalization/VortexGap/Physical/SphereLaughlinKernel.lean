import VortexGap.Geometry.SphereAffineContact
import VortexGap.Geometry.SphereChartHeads
import VortexGap.Physical.SphereContactGap
import VortexGap.Physical.SphereZeroTransport

noncomputable section
namespace VortexGap.Fermion
open MeasureTheory OAI.Laughlin.Rotation VortexGap.SpherePolynomial
open scoped ENNReal

theorem sphere_reference_zero_iff_chart {n N : ℕ} (x : particleSector (n+2) (N+2)) :
    sphereSectorHam n (N+2) (sphereOrbitPair n) x = 0 ↔ ∀ s a, chartHeadJet x s a = 0 := by
  let _ : Measure.IsOpenPosMeasure (spherePairMeasure n) :=
    Measure.isOpenPosMeasure_smul sourceHaar (ENNReal.ofReal_ne_zero_iff.mpr (by positivity))
  rw [← Submodule.coe_eq_zero,sphereSectorHam_apply _ _ (sphereOrbitPair_continuous n)]
  rw [continuousContact_zero_iff_all_spectators _ _ (sphereOrbitPair_continuous n)
    ((sphereOrbitPair_continuous n).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  exact all_contractions_iff_chartHeadJet x

theorem sphere_reference_laughlin_kernel (n N : ℕ) (hQ : 3*((N+2)-1) = n+1) :
    ∃ l : particleSector (n+2) (N+2), l ≠ 0 ∧ sectorPoly l = laughlin (N+2) ∧
      LinearMap.ker (sphereSectorHam n (N+2) (sphereOrbitPair n)).toLinearMap = ℂ ∙ l := by
  have h := sector_chart_jet_line N
  rw [hQ] at h
  obtain ⟨l,hn,hp,hl⟩ := h
  refine ⟨l,hn,hp,?_⟩
  ext x
  rw [LinearMap.mem_ker, Submodule.mem_span_singleton]
  change sphereSectorHam n (N+2) (sphereOrbitPair n) x = 0 ↔ _
  rw [sphere_reference_zero_iff_chart,hl]
  exact exists_congr fun c => eq_comm

theorem sphere_reference_laughlin_unique (n N : ℕ) (hQ : 3*((N+2)-1) = n+1) :
    Module.finrank ℂ (LinearMap.ker (sphereSectorHam n (N+2) (sphereOrbitPair n)).toLinearMap) = 1 := by
  obtain ⟨l,hn,_,h⟩ := sphere_reference_laughlin_kernel n N hQ
  rw [h,finrank_span_singleton hn]

/-- Three particles, seven orbitals and flux six. -/
theorem sphere_reference_three_flux_six :
    Module.finrank ℂ (LinearMap.ker (sphereSectorHam 5 3 (sphereOrbitPair 5)).toLinearMap) = 1 :=
  sphere_reference_laughlin_unique 5 1 (by decide)
end VortexGap.Fermion
end

noncomputable section
namespace VortexGap.Fermion
open OAI.Laughlin.Rotation VortexGap.SpherePolynomial

/-- The physical line is the exterior Gram square root applied to the
reference Laughlin generator, in the orthonormal sector coordinates. -/
theorem sphere_deformed_laughlin_kernel (n N : ℕ) (hQ : 3*((N+2)-1) = n+1)
    (f : SourceSU2 → ℂ) (hf : Continuous f) (a b : ℝ)
    (ha : 0 < a) (hl : ∀ g, a ≤ ‖f g‖^2) (hu : ∀ g, ‖f g‖^2 ≤ b) :
    let S := (CFC.sqrt (gramOperator (sphereScalarMap (n+1) f hf))).toLinearMap
    ∃ l : particleSector (n+2) (N+2), l ≠ 0 ∧ sectorPoly l = laughlin (N+2) ∧
      LinearMap.ker (sphereSectorHam n (N+2) (spherePhysicalPair n f hf)).toLinearMap =
        ℂ ∙ exteriorPower S (N+2) l := by
  dsimp only
  obtain ⟨l,hn,hp,hker⟩ := sphere_reference_laughlin_kernel n N hQ
  refine ⟨l,hn,hp,?_⟩
  let F := sphereScalarMap (n+1) f hf
  let S := (CFC.sqrt (gramOperator F)).toLinearMap
  let R := (gramInvSqrt F).toLinearMap
  have hF := gramOperator_strict F a ha (sphereScalarGram_bounds (n+1) f hf a b ha.le hl hu).1
  have hSR : S.comp R = LinearMap.id := congrArg ContinuousLinearMap.toLinearMap (gramInvSqrt_right F hF)
  have ht := (spherePhysical_zero_transport n (N+2) f hf a b ha hl hu).1
  rw [hker] at ht
  have hh := congrArg (Submodule.map (exteriorPower S (N+2))) ht
  rw [← Submodule.map_comp,← exteriorPower_comp,hSR,exteriorPower_id,Submodule.map_id,
    Submodule.map_span,Set.image_singleton] at hh
  exact hh

theorem sphere_deformed_laughlin_unique (n N : ℕ) (hQ : 3*((N+2)-1) = n+1)
    (f : SourceSU2 → ℂ) (hf : Continuous f) (a b : ℝ)
    (ha : 0 < a) (hl : ∀ g, a ≤ ‖f g‖^2) (hu : ∀ g, ‖f g‖^2 ≤ b) :
    Module.finrank ℂ (LinearMap.ker (sphereSectorHam n (N+2) (spherePhysicalPair n f hf)).toLinearMap) = 1 :=
  (spherePhysical_zero_transport n (N+2) f hf a b ha hl hu).2.trans
    (sphere_reference_laughlin_unique n N hQ)

theorem sphere_axial_three_flux_six_unique :
    Module.finrank ℂ (LinearMap.ker (sphereSectorHam 5 3 (spherePhysicalPair 5
      sphereAxialMultiplier sphereAxialMultiplier_continuous)).toLinearMap) = 1 :=
  (sphereAxial_zero_multiplicity 5 3).trans sphere_reference_three_flux_six

end VortexGap.Fermion
end
