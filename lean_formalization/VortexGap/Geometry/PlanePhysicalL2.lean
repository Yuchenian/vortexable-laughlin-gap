import VortexGap.Geometry.PlanePhysicalScale
import VortexGap.Geometry.PlaneMeasurability
import VortexGap.Frame.BesselAnalysis
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory

theorem planeEvaluation_continuous (ell : ℝ) : Continuous (planeEvaluation ell) := by
  unfold planeEvaluation
  have hc : Continuous (fun z : ℂ => (starRingEnd ℂ) (planeCoordinate ell z)) := by
    unfold planeCoordinate
    fun_prop
  exact (continuous_const : Continuous (fun _ : ℂ => ((Real.sqrt (2*Real.pi*ell^2))⁻¹ : ℂ))).smul
    (planeCoherent_continuous.comp hc)

theorem planeEvaluation_coefficient_memLp (ell : ℝ) (hell : 0 < ell) (v : CountableOrbital) :
    MemLp (fun z => inner ℂ (planeEvaluation ell z) v) 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm
    ((planeEvaluation_continuous ell).inner continuous_const).aestronglyMeasurable).2
  by_cases hv : v = 0
  · subst v
    simp
  · apply Integrable.of_integral_ne_zero
    rw [planeEvaluation_integral_norm_sq ell hell v]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hv)

/-- Actual physical LLL embedding into Lebesgue L2; the full oscillator l2 is retained. -/
def planeLLLEmbedding (ell : ℝ) (hell : 0 < ell) : CountableOrbital →ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℂ) where
  toLinearMap := Frame.besselAnalysisLinear volume (fun z => innerSL ℂ (planeEvaluation ell z))
    (planeEvaluation_coefficient_memLp ell hell)
  norm_map' v := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    exact (Frame.besselAnalysisLinear_norm_sq volume (fun z => innerSL ℂ (planeEvaluation ell z))
      (planeEvaluation_coefficient_memLp ell hell) v).trans (planeEvaluation_integral_norm_sq ell hell v)

theorem planeLLLEmbedding_coe (ell : ℝ) (hell : 0 < ell) (v : CountableOrbital) :
    planeLLLEmbedding ell hell v =ᵐ[volume] (fun z => inner ℂ (planeEvaluation ell z) v) :=
  Frame.besselAnalysisLinear_ae _ _ _ v

theorem planeLLLEmbedding_norm (ell : ℝ) (hell : 0 < ell) (v : CountableOrbital) :
    ‖planeLLLEmbedding ell hell v‖ = ‖v‖ := (planeLLLEmbedding ell hell).norm_map v

theorem planeLLLEmbedding_inner (ell : ℝ) (hell : 0 < ell) (v w : CountableOrbital) :
    inner ℂ (planeLLLEmbedding ell hell v) (planeLLLEmbedding ell hell w) = inner ℂ v w :=
  (planeLLLEmbedding ell hell).inner_map_map v w

theorem planeLLLEmbedding_basis (ell : ℝ) (hell : 0 < ell) (n : ℕ) :
    planeLLLEmbedding ell hell (orbitalKet n) =ᵐ[volume] (fun z => planeWavefunction ell z n) := by
  filter_upwards [planeLLLEmbedding_coe ell hell (orbitalKet n)] with z hz
  rw [hz, ← inner_conj_symm, orbitalKet_inner_left, planeEvaluation_coefficient]
  simp

theorem planeLLLEmbedding_range_closed (ell : ℝ) (hell : 0 < ell) :
    IsClosed ((planeLLLEmbedding ell hell).toLinearMap.range : Set (Lp ℂ 2 (volume : Measure ℂ))) :=
  (planeLLLEmbedding ell hell).isometry.isClosedEmbedding.isClosed_range

end VortexGap.Fermion




