import VortexGap.Examples.PlaneWeakCosine
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped InnerProduct ComplexOrder BoundedContinuousFunction

/-- Projected two-body coercivity fixes the kernel on every finite sector. -/
theorem planeBandContact_kernel_filtered (ell : ℝ) (hell : 0 < ell) (f : ℂ →ᵇ ℂ)
    (hG : IsStrictlyPositive (planeScalarGram ell hell f)) (hf : Differentiable ℝ f)
    (κ : ℝ) (hκ : 0 < κ) (hw : (κ : ℂ) • planePairOperator ≤ planeWeightedPairOperator ell f)
    (N : ℕ) :
    LinearMap.ker (planeBandContactOperator ell hell f hG hf N).toLinearMap =
      LinearMap.ker (filteredPairHamiltonian N (gramInvSqrt (planeScalarEmbedding ell hell f))
        (gramInvSqrt_nonneg _ hG) planePairOperator).toLinearMap := by
  let R := gramInvSqrt (planeScalarEmbedding ell hell f)
  have hR : 0 ≤ R := gramInvSqrt_nonneg _ hG
  let B := filteredPairHamiltonian N R hR planePairOperator
  let A := filteredPairHamiltonian N R hR (planeWeightedPairOperator ell f)
  have ha : 0 ≤ A := ContinuousLinearMap.nonneg_iff_isPositive.mpr
    (filteredPairHamiltonian_positive N R hR _ (planeWeightedPairOperator_positive ell f))
  have hb : 0 ≤ B := ContinuousLinearMap.nonneg_iff_isPositive.mpr
    (filteredPairHamiltonian_positive N R hR _ planePairOperator_positive)
  have hc := filteredPairHamiltonian_coercivity N R hR planePairOperator
    (planeWeightedPairOperator ell f) κ (‖f‖^4) hw
    (by simpa only [Complex.ofReal_pow] using planeWeightedPairOperator_upper ell f)
  rw [planeBandContactOperator, planeScalarContactOperator_eq_pairLift]
  exact positive_form_comparison_kernel A B ha hb κ _ hκ
    (operator_scaled_le_energy B A κ hc.1) (operator_le_scaled_energy A B _ hc.2)

/-- Pair coordinates test the exact two-particle zero-mode condition. -/
theorem planeBandContact_two_zero_iff (ell : ℝ) (hell : 0 < ell) (f : ℂ →ᵇ ℂ)
    (hG : IsStrictlyPositive (planeScalarGram ell hell f)) (hf : Differentiable ℝ f)
    (κ : ℝ) (hκ : 0 < κ) (hw : (κ : ℂ) • planePairOperator ≤ planeWeightedPairOperator ell f)
    (p : CountablePairSpace) :
    planeBandContactOperator ell hell f hG hf 2
      ⟨countablePairEmbedding p, countablePairEmbedding_sector p⟩ = 0 ↔
    planePairOperator (countablePairFilter (gramInvSqrt (planeScalarEmbedding ell hell f))
      (gramInvSqrt_nonneg _ hG) p) = 0 := by
  let R := gramInvSqrt (planeScalarEmbedding ell hell f)
  have hR : 0 ≤ R := gramInvSqrt_nonneg _ hG
  let D := countablePairFilter R hR
  let T := D.adjoint.comp (planePairOperator.comp D)
  let x : countableSector 2 := ⟨countablePairEmbedding p, countablePairEmbedding_sector p⟩
  change x ∈ LinearMap.ker (planeBandContactOperator ell hell f hG hf 2).toLinearMap ↔ _
  rw [planeBandContact_kernel_filtered ell hell f hG hf κ hκ hw]
  change countablePairLift 2 T ⟨countablePairEmbedding p, countablePairEmbedding_sector p⟩ = 0 ↔ _
  rw [countablePairLift_pairEmbedding]
  constructor
  · intro h
    have hp : T p = 0 := countablePairEmbedding.injective
      ((congrArg Subtype.val h).trans (map_zero countablePairEmbedding).symm)
    apply (positive_energy_zero_iff planePairOperator
      (ContinuousLinearMap.nonneg_iff_isPositive.mpr planePairOperator_positive) (D p)).mp
    have he : inner ℂ (D p) (planePairOperator (D p)) = inner ℂ p (T p) :=
      (ContinuousLinearMap.adjoint_inner_right D _ _).symm
    rw [he, hp, inner_zero_right, Complex.zero_re]
  · intro h
    apply Subtype.ext
    change countablePairEmbedding (D.adjoint (planePairOperator (D p))) = 0
    change planePairOperator (D p) = 0 at h
    simp [h]

theorem planeWeakCos_two_zero_iff (ell : ℝ) (hell : 0 < ell) (p : CountablePairSpace) :
    planeWeakCosContactOperator ell hell 2
      ⟨countablePairEmbedding p, countablePairEmbedding_sector p⟩ = 0 ↔
    planePairOperator (countablePairFilter (gramInvSqrt (planeScalarEmbedding ell hell planeWeakCos))
      (gramInvSqrt_nonneg _ (gramOperator_strict _ ((9999/10000 : ℝ)^2) (by norm_num)
        (planeWeakCos_gram_bounds ell hell).1)) p) = 0 := by
  exact planeBandContact_two_zero_iff ell hell planeWeakCos _ planeWeakCos_differentiable
    ((9999/10000 : ℝ)^4) (by positivity) (planeWeakCos_coercivity ell) p
end VortexGap.Fermion

