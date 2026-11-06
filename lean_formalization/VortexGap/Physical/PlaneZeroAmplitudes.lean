import VortexGap.Physical.PlaneExteriorZeroImage
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped InnerProduct ComplexOrder BoundedContinuousFunction

/-- Ordered field amplitude, before the common N-particle normalization.
The first listed field acts first, and the empty list evaluates the vacuum component. -/
def planeOrderedAmplitude (field : ℂ → CountableSpace →L[ℂ] CountableSpace) :
    List ℂ → CountableSpace →L[ℂ] ℂ
  | [] => lp.evalCLM ℂ _ 2 ∅
  | z :: zs => (planeOrderedAmplitude field zs).comp (field z)

private theorem vacuum_coefficient_compression (M : CountableOrbital →L[ℂ] CountableOrbital)
    (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1) (x : CountableSpace) :
    (countableFockCompression M hM hc x) ∅ = x ∅ := by
  let J := countableLossEmbedding M hM hc
  rw [← countableKet_inner_left, ← countableKet_inner_left ∅ x]
  change inner ℂ (countableKet ∅) ((countableFockIsometry countableSysOrbital).toContinuousLinearMap.adjoint
    (countableFockIsometry J x)) = _
  rw [ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ (countableFockIsometry countableSysOrbital (countableKet ∅)) _ = _
  rw [countableFockIsometry_vacuum, ← countableFockIsometry_vacuum J, countableFockIsometry_inner, countableFockIsometry_vacuum]

theorem planeBand_orderedAmplitude_product (ell : ℝ) (hell : 0 < ell) (f : ℂ →ᵇ ℂ)
    (hG : IsStrictlyPositive (planeScalarGram ell hell f)) (zs : List ℂ) (x : CountableSpace) :
    planeOrderedAmplitude (planeBandField ell hell f hG) zs
      (countableDegreeFilter zs.length (gramRoot (planeScalarEmbedding ell hell f)) (gramRoot_nonneg _) x) =
      (zs.map (fun z => f z)).prod * planeOrderedAmplitude (planeField ell) zs x := by
  let F := planeScalarEmbedding ell hell f
  let S := gramRoot F
  have hS : 0 ≤ S := gramRoot_nonneg F
  have hi (v : CountableOrbital) : S (gramInvSqrt F v) = v :=
    congrArg (fun T : CountableOrbital →L[ℂ] CountableOrbital => T v) (gramInvSqrt_right F hG)
  induction zs generalizing x with
  | nil =>
    change (countableDegreeFilter 0 S hS x) ∅ = 1 * x ∅
    simp only [countableDegreeFilter, pow_zero, one_smul, one_mul]
    apply vacuum_coefficient_compression
  | cons z zs ih =>
    change planeOrderedAmplitude _ zs (planeBandField ell hell f hG z
      (countableDegreeFilter (zs.length+1) S hS x)) = _
    rw [planeBandField_eq_filtered, smul_apply, map_smul]
    change (f z) * (planeOrderedAmplitude _ zs (countableAnnihilate (gramInvSqrt F (planeEvaluation ell z))
      (countableDegreeFilter (zs.length+1) S hS x))) = _
    rw [countableDegreeFilter_annihilate, hi]
    change (f z) * (planeOrderedAmplitude _ zs (countableDegreeFilter zs.length
      (gramRoot (planeScalarEmbedding ell hell f)) (gramRoot_nonneg _) (planeField ell z x))) = _
    rw [ih]
    simp only [List.map_cons, List.prod_cons, planeOrderedAmplitude, ContinuousLinearMap.comp_apply, mul_assoc]

/-- Position-space representative obtained by evaluating N annihilation fields
on an ordered configuration with the usual inverse square-root factorial. -/
def planeConfigurationAmplitude (field : ℂ → CountableSpace →L[ℂ] CountableSpace) {N : ℕ}
    (x : countableSector N) (z : Fin N → ℂ) : ℂ :=
  (Real.sqrt N.factorial : ℂ)⁻¹ * planeOrderedAmplitude field (List.ofFn z) x

theorem planeBand_configuration_product (ell : ℝ) (hell : 0 < ell) (f : ℂ →ᵇ ℂ)
    (hG : IsStrictlyPositive (planeScalarGram ell hell f)) (N : ℕ) (x : countableSector N)
    (z : Fin N → ℂ) :
    planeConfigurationAmplitude (planeBandField ell hell f hG)
      (countableExteriorFilter N (gramRoot (planeScalarEmbedding ell hell f)) (gramRoot_nonneg _) x) z =
    (∏ i, f (z i)) * planeConfigurationAmplitude (planeField ell) x z := by
  have hp := planeBand_orderedAmplitude_product ell hell f hG (List.ofFn z) x
  simp only [List.length_ofFn, List.map_ofFn, List.prod_ofFn, Function.comp_apply] at hp
  unfold planeConfigurationAmplitude
  change _ * (planeOrderedAmplitude _ (List.ofFn z) (countableDegreeFilter N (gramRoot (planeScalarEmbedding ell hell f)) (gramRoot_nonneg _) x)) = _
  rw [hp]
  ring

/-- Equality of the two sets of zero-energy configuration amplitudes. -/
theorem planeBand_zero_configuration_image (ell : ℝ) (hell : 0 < ell) (f : ℂ →ᵇ ℂ)
    (hG : IsStrictlyPositive (planeScalarGram ell hell f)) (hf : Differentiable ℝ f)
    (κ : ℝ) (hκ : 0 < κ) (hw : (κ : ℂ) • planePairOperator ≤ planeWeightedPairOperator ell f)
    (N : ℕ) (ψ : (Fin N → ℂ) → ℂ) :
    (∃ x : countableSector N, planeBandContactOperator ell hell f hG hf N x = 0 ∧
      ψ = planeConfigurationAmplitude (planeBandField ell hell f hG) x) ↔
    ∃ y : countableSector N, countablePairLift N planePairOperator y = 0 ∧
      ψ = fun z => (∏ i, f (z i)) * planeConfigurationAmplitude (planeField ell) y z := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨y, hy, rfl⟩ := (planeBandContact_zero_iff_exteriorImage ell hell f hG hf κ hκ hw N x).mp hx
    exact ⟨y, hy, funext (planeBand_configuration_product ell hell f hG N y)⟩
  · rintro ⟨y, hy, rfl⟩
    refine ⟨_, (planeBandContact_zero_iff_exteriorImage ell hell f hG hf κ hκ hw N _).mpr
      ⟨y, hy, rfl⟩, ?_⟩
    exact (funext (planeBand_configuration_product ell hell f hG N y)).symm

end VortexGap.Fermion
