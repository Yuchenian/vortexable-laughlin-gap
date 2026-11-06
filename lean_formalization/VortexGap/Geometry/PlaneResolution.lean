import VortexGap.Geometry.PlaneBessel
import VortexGap.Frame.CountableContinuousPair
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory
open scoped ENNReal

/-- Weak integral of the actual coherent pair frame, using the proved beta=1 data. -/
def planePairOperator : CountablePairSpace →L[ℂ] CountablePairSpace :=
  countableContinuousPairOperator planePairMeasure
    (fun z => countableTwoFramePair (planeTwoFrame z)) planePair_coefficient_memLp
    1 (by norm_num) (fun q => by simpa only [one_mul] using planePair_bessel q)

theorem planePairOperator_positive : planePairOperator.IsPositive :=
  countableContinuousPairOperator_positive _ _ _ _ _ _

theorem planePairOperator_energy (q : CountablePairSpace) :
    (inner ℂ q (planePairOperator q)).re = ‖planePairRightCoordinates q‖^2 := by
  rw [planePairOperator, countableContinuousPairOperator_energy]
  simp_rw [norm_inner_symm (countableTwoFramePair (planeTwoFrame _)) q]
  exact planePair_right_coefficient_integral q

theorem planeBlockSynthesis_single (n : ℕ) :
    planeBlockSynthesis (lp.single 2 n 1) = planeBlockVector (n+1) := by
  simp [planeBlockSynthesis, OrthogonalFamily.linearIsometry_apply_single,
    LinearIsometry.toSpanSingleton_apply]

theorem planeBlockSynthesis_adjoint_coordinate (q : CountablePairSpace) (n : ℕ) :
    planeBlockSynthesis.toContinuousLinearMap.adjoint q n =
      inner ℂ (planeBlockVector (n+1)) q := by
  have h := ContinuousLinearMap.adjoint_inner_right planeBlockSynthesis.toContinuousLinearMap
    (lp.single 2 n 1) q
  simpa only [lp.inner_single_left, map_one, one_mul,
    LinearIsometry.coe_toContinuousLinearMap, planeBlockSynthesis_single, RCLike.inner_apply', map_one, one_mul] using h

theorem planeBlockSynthesis_adjoint_norm_sq (q : CountablePairSpace) :
    ‖planeBlockSynthesis.toContinuousLinearMap.adjoint q‖^2 = ‖planePairRightCoordinates q‖^2 := by
  have hl (v : CountableOrbital) : ‖v‖^2 = ∑' n, ‖v n‖^2 := by
    simpa using lp.norm_rpow_eq_tsum (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal) v
  rw [hl, hl]
  apply tsum_congr
  intro n
  rw [planeBlockSynthesis_adjoint_coordinate]
  change ‖inner ℂ (planeBlockVector (n+1)) q‖^2 = ‖inner ℂ q (planeBlockVector (n+1))‖^2
  rw [norm_inner_symm]

/-- Resolution as the projection onto the actual closed angular-block span. -/
theorem planePairOperator_eq_block_projection :
    planePairOperator = planeBlockSynthesis.toContinuousLinearMap.comp
      planeBlockSynthesis.toContinuousLinearMap.adjoint := by
  let S := planeBlockSynthesis.toContinuousLinearMap
  have hp : (S.comp S.adjoint).IsPositive := by
    simpa only [ContinuousLinearMap.adjoint_adjoint] using
      ContinuousLinearMap.isPositive_adjoint_comp_self S.adjoint
  apply ContinuousLinearMap.coe_injective
  apply (ext_inner_map _ _).mp
  intro q
  have hq := planePairOperator_positive.toLinearMap.isSymmetric
  have hproj := hp.toLinearMap.isSymmetric
  rw [← hq.coe_re_inner_apply_self, ← hproj.coe_re_inner_apply_self]
  congr 1
  rw [inner_re_symm]
  change (inner ℂ q (planePairOperator q)).re = (inner ℂ (S (S.adjoint q)) q).re
  rw [planePairOperator_energy]
  rw [← ContinuousLinearMap.adjoint_inner_right, ← RCLike.re_eq_complex_re,
    ← norm_sq_eq_re_inner (𝕜 := ℂ)]
  exact (planeBlockSynthesis_adjoint_norm_sq q).symm

theorem planeBlockSynthesis_adjoint_synthesis (v : CountableOrbital) :
    planeBlockSynthesis.toContinuousLinearMap.adjoint (planeBlockSynthesis v) = v := by
  exact congrArg (fun T : CountableOrbital →L[ℂ] CountableOrbital => T v)
    planeBlockSynthesis.adjoint_comp_self

theorem planePairOperator_on_block_span (v : CountableOrbital) :
    planePairOperator (planeBlockSynthesis v) = planeBlockSynthesis v := by
  rw [planePairOperator_eq_block_projection, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, planeBlockSynthesis_adjoint_synthesis]

theorem planePairOperator_idempotent : planePairOperator * planePairOperator = planePairOperator := by
  apply ContinuousLinearMap.ext
  intro q
  change planePairOperator (planePairOperator q) = planePairOperator q
  have h : planePairOperator q =
      planeBlockSynthesis (planeBlockSynthesis.toContinuousLinearMap.adjoint q) := by
    rw [planePairOperator_eq_block_projection]
    rfl
  calc
    planePairOperator (planePairOperator q) =
        planePairOperator (planeBlockSynthesis (planeBlockSynthesis.toContinuousLinearMap.adjoint q)) :=
      congrArg planePairOperator h
    _ = planeBlockSynthesis (planeBlockSynthesis.toContinuousLinearMap.adjoint q) :=
      planePairOperator_on_block_span _
    _ = planePairOperator q := h.symm
theorem planePairOperator_range :
    Set.range planePairOperator = Set.range planeBlockSynthesis := by
  ext q
  constructor
  · rintro ⟨r, rfl⟩
    refine ⟨planeBlockSynthesis.toContinuousLinearMap.adjoint r, ?_⟩
    rw [planePairOperator_eq_block_projection]
    rfl
  · rintro ⟨v, rfl⟩
    exact ⟨planeBlockSynthesis v, planePairOperator_on_block_span v⟩

end VortexGap.Fermion






