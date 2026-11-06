import VortexGap.Fermion.CountableFieldParseval
import VortexGap.Physical.PlaneBandField
import VortexGap.Physical.PlaneConfigurationL2

noncomputable section
namespace VortexGap.Fermion
open MeasureTheory
open scoped ENNReal ComplexOrder BoundedContinuousFunction
variable (ell : ℝ) (hell : 0<ell) (f : ℂ →ᵇ ℂ) (hG : IsStrictlyPositive (planeScalarGram ell hell f))
  (x : CountableSpace) (A : Finset ℕ)

theorem bandField_probe (z : ℂ) :
    planeBandField ell hell f hG z x A =
      f z * inner ℂ (planeEvaluation ell z)
        (gramInvSqrt (planeScalarEmbedding ell hell f) ((creationProbe (countableKet A)).adjoint x)) := by
  rw [planeBandField_eq_filtered]
  change f z * (countableAnnihilate _ x A) = _
  congr 1
  rw [← countableKet_inner_left, fieldProbe_value]
  exact (ContinuousLinearMap.nonneg_iff_isPositive.mp (gramInvSqrt_nonneg _ hG)).inner_left_eq_inner_right _ _

theorem planeBandField_probe_memLp :
    MemLp (fun z => planeBandField ell hell f hG z x A) 2 volume := by
  simp_rw [bandField_probe]
  exact planeScalar_coefficient_memLp ell hell f _

theorem planeBandField_coefficient_parseval :
    (∫ z : ℂ, ‖planeBandField ell hell f hG z x A‖^2) = ∑' i, ‖countableAnnihilateMode i x A‖^2 := by
  let v := (creationProbe (countableKet A)).adjoint x
  let R := gramInvSqrt (planeScalarEmbedding ell hell f)
  have h := Frame.besselAnalysis_norm_sq volume (fun z => f z • innerSL ℂ (planeEvaluation ell z))
    (planeScalar_coefficient_memLp ell hell f) (‖f‖^2) (sq_nonneg _) (planeScalar_coefficient_bound ell hell f) (R v)
  change ‖planeScalarEmbedding ell hell f (R v)‖^2 = ∫ z, ‖f z * inner ℂ (planeEvaluation ell z) (R v)‖^2 at h
  have hi : ‖planeScalarEmbedding ell hell f (R v)‖ = ‖v‖ := (planeScalarUnitary ell hell f hG).norm_map v
  have hm (i : ℕ) : countableAnnihilateMode i x A = v i := by
    rw [← countableAnnihilate_ket,← countableKet_inner_left,fieldProbe_value,orbitalKet_inner_left]
  simp_rw [bandField_probe,hm]
  change (∫ z, ‖f z * inner ℂ (planeEvaluation ell z) (R v)‖^2) = _
  rw [← h,hi]
  simpa using lp.norm_rpow_eq_tsum (by norm_num : (0:ℝ)<(2:ℝ≥0∞).toReal) v

theorem planeBandField_integral_number {N : ℕ} (hx : x ∈ countableSector N) :
    (∫ z : ℂ, ‖planeBandField ell hell f hG z x‖^2) = (N:ℝ)*‖x‖^2 := by
  apply field_integral_of_coefficient_parseval x hx _ _ (planeBandField_coefficient_parseval ell hell f hG x)
  intro B
  have h := planeBandField_probe_memLp ell hell f hG x B
  exact (memLp_two_iff_integrable_sq_norm h.aestronglyMeasurable).mp h

end VortexGap.Fermion
end

noncomputable section
namespace VortexGap.Fermion
open MeasureTheory
open scoped ComplexOrder BoundedContinuousFunction
variable (ell : ℝ) (hell : 0<ell) (f : ℂ →ᵇ ℂ) (hG : IsStrictlyPositive (planeScalarGram ell hell f))
private theorem bandContinuous : Continuous (planeBandField ell hell f hG) := by
  change Continuous (fun z => planeBandField ell hell f hG z)
  simp only [planeBandField_eq_filtered,planeFilteredField]
  exact f.continuous.smul (countableAnnihilate_continuous.comp
    ((gramInvSqrt (planeScalarEmbedding ell hell f)).continuous.comp (planeEvaluation_continuous ell)))

private theorem bandLower {n : ℕ} (z : ℂ) (x : CountableSpace) (hx : x ∈ countableSector (n+1)) :
    planeBandField ell hell f hG z x ∈ countableSector n := countableAnnihilate_sector _ hx

private theorem bandMem {n : ℕ} (x : CountableSpace) (hx : x ∈ countableSector n) :
    MemLp (fun z => planeBandField ell hell f hG z x) 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm ((bandContinuous ell hell f hG).clm_apply
    (g := fun _ => x) continuous_const).aestronglyMeasurable).mpr
  cases n with
  | zero =>
    have h (z) : planeBandField ell hell f hG z x = 0 := countableAnnihilate_zero_sector _ hx
    simp [h]
  | succ n =>
    by_cases he : x=0
    · subst x; simp
    · apply Integrable.of_integral_ne_zero
      rw [planeBandField_integral_number ell hell f hG x hx]
      exact mul_ne_zero (by positivity) (pow_ne_zero _ (norm_ne_zero_iff.mpr he))

include ell hell f hG in
def planeBandConfigurationL2 (N : ℕ) : countableSector N →ₗᵢ[ℂ] Lp ℂ 2 (planeConfigMeasure N) :=
  OrderedField.planeReferenceConfigurationL2 _ (bandContinuous ell hell f hG) (bandLower ell hell f hG)
    (bandMem ell hell f hG) (fun x hx => planeBandField_integral_number ell hell f hG x hx) N

theorem planeBandConfigurationL2_ae {N : ℕ} (x : countableSector N) :
    planeBandConfigurationL2 ell hell f hG N x =ᵐ[planeConfigMeasure N]
      planeConfigurationAmplitude (planeBandField ell hell f hG) x :=
  OrderedField.planeReferenceConfigurationL2_ae _ (bandContinuous ell hell f hG) (bandLower ell hell f hG)
    (bandMem ell hell f hG) (fun x hx => planeBandField_integral_number ell hell f hG x hx) x

theorem planeBandConfigurationL2_product {N : ℕ} (x : countableSector N) :
    planeBandConfigurationL2 ell hell f hG N
      (countableExteriorFilter N (gramRoot (planeScalarEmbedding ell hell f)) (gramRoot_nonneg _) x)
      =ᵐ[planeConfigMeasure N] fun z => (∏ i, f (z i)) * planeReferenceConfigurationL2 ell hell N x z := by
  filter_upwards [planeBandConfigurationL2_ae ell hell f hG
    (countableExteriorFilter N (gramRoot (planeScalarEmbedding ell hell f)) (gramRoot_nonneg _) x),
    planeReferenceConfigurationL2_ae ell hell x] with z hz hr
  rw [hz,hr,planeBand_configuration_product]

theorem planeBand_zero_L2_image (hf : Differentiable ℝ f) (κ : ℝ) (hκ : 0<κ)
    (hw : (κ : ℂ) • planePairOperator ≤ planeWeightedPairOperator ell f)
    (N : ℕ) (ψ : Lp ℂ 2 (planeConfigMeasure N)) :
    (∃ x : countableSector N, planeBandContactOperator ell hell f hG hf N x = 0 ∧
      ψ = planeBandConfigurationL2 ell hell f hG N x) ↔
    ∃ y : countableSector N, countablePairLift N planePairOperator y = 0 ∧
      ψ =ᵐ[planeConfigMeasure N] fun z => (∏ i, f (z i)) * planeReferenceConfigurationL2 ell hell N y z := by
  constructor
  · rintro ⟨x,hx,rfl⟩
    obtain ⟨y,hy,rfl⟩ := (planeBandContact_zero_iff_exteriorImage ell hell f hG hf κ hκ hw N x).mp hx
    exact ⟨y,hy,planeBandConfigurationL2_product ell hell f hG y⟩
  · rintro ⟨y,hy,he⟩
    exact ⟨_,(planeBandContact_zero_iff_exteriorImage ell hell f hG hf κ hκ hw N _).mpr ⟨y,hy,rfl⟩,
      Lp.ext (he.trans (planeBandConfigurationL2_product ell hell f hG y).symm)⟩

theorem planeWeakCos_zero_L2_image (N : ℕ) (ψ : Lp ℂ 2 (planeConfigMeasure N)) :
    let h := gramOperator_strict _ ((9999/10000 : ℝ)^2) (by norm_num) (planeWeakCos_gram_bounds ell hell).1
    (∃ x : countableSector N, planeWeakCosContactOperator ell hell N x = 0 ∧
      ψ = planeBandConfigurationL2 ell hell planeWeakCos h N x) ↔
    ∃ y : countableSector N, countablePairLift N planePairOperator y = 0 ∧
      ψ =ᵐ[planeConfigMeasure N] fun z => (∏ i, planeWeakCos (z i)) * planeReferenceConfigurationL2 ell hell N y z :=
  planeBand_zero_L2_image ell hell planeWeakCos _ planeWeakCos_differentiable
    ((9999/10000 : ℝ)^4) (by positivity) (planeWeakCos_coercivity ell) N ψ

end VortexGap.Fermion
end
