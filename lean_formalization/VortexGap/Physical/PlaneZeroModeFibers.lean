import VortexGap.Physical.PlaneZeroModes
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped InnerProduct ComplexOrder BoundedContinuousFunction

theorem positive_congruence_zero_iff {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (D : H →L[ℂ] K) (Q : K →L[ℂ] K) (hQ : Q.IsPositive) (x : H) :
    D.adjoint (Q (D x)) = 0 ↔ Q (D x) = 0 := by
  constructor
  · intro h
    apply (positive_energy_zero_iff Q (ContinuousLinearMap.nonneg_iff_isPositive.mpr hQ) _).mp
    rw [← ContinuousLinearMap.adjoint_inner_right, h, inner_zero_right, Complex.zero_re]
  · intro h
    rw [h, map_zero]

/-- The two-annihilation amplitudes at each spectator occupation separately
test membership in the many-body kernel of a positive pair lift. -/
theorem countablePairLift_zero_iff_fibers (N : ℕ) (Q : CountablePairSpace →L[ℂ] CountablePairSpace)
    (hQ : Q.IsPositive) (x : countableSector N) :
    countablePairLift N Q x = 0 ↔ ∀ A : Finset ℕ, Q (countablePairFiber (countablePairStack N x) A) = 0 := by
  change (countablePairStack N).adjoint (countablePairAmplify Q (countablePairStack N x)) = 0 ↔ _
  rw [positive_congruence_zero_iff _ _ (countablePairAmplify_positive Q hQ) x]
  constructor
  · intro h A
    ext a
    exact congrArg (fun z : CountablePairStackSpace => z a A) h
  · intro h
    ext a A
    exact congrArg (fun p : CountablePairSpace => p a) (h A)

theorem planeBandContact_zero_iff_fibers (ell : ℝ) (hell : 0 < ell) (f : ℂ →ᵇ ℂ)
    (hG : IsStrictlyPositive (planeScalarGram ell hell f)) (hf : Differentiable ℝ f)
    (κ : ℝ) (hκ : 0 < κ) (hw : (κ : ℂ) • planePairOperator ≤ planeWeightedPairOperator ell f)
    (N : ℕ) (x : countableSector N) :
    planeBandContactOperator ell hell f hG hf N x = 0 ↔ ∀ A : Finset ℕ,
      planePairOperator (countablePairFilter (gramInvSqrt (planeScalarEmbedding ell hell f))
        (gramInvSqrt_nonneg _ hG) (countablePairFiber (countablePairStack N x) A)) = 0 := by
  let D := countablePairFilter (gramInvSqrt (planeScalarEmbedding ell hell f)) (gramInvSqrt_nonneg _ hG)
  change x ∈ LinearMap.ker (planeBandContactOperator ell hell f hG hf N).toLinearMap ↔ _
  rw [planeBandContact_kernel_filtered ell hell f hG hf κ hκ hw]
  change countablePairLift N (D.adjoint.comp (planePairOperator.comp D)) x = 0 ↔ _
  rw [countablePairLift_zero_iff_fibers _ _ (planePairOperator_positive.adjoint_conj D)]
  exact forall_congr' (fun A => positive_congruence_zero_iff D _ planePairOperator_positive _)

theorem planeWeakCos_zero_iff_fibers (ell : ℝ) (hell : 0 < ell) (N : ℕ) (x : countableSector N) :
    planeWeakCosContactOperator ell hell N x = 0 ↔ ∀ A : Finset ℕ,
      planePairOperator (countablePairFilter (gramInvSqrt (planeScalarEmbedding ell hell planeWeakCos))
        (gramInvSqrt_nonneg _ (gramOperator_strict _ ((9999/10000 : ℝ)^2) (by norm_num)
          (planeWeakCos_gram_bounds ell hell).1)) (countablePairFiber (countablePairStack N x) A)) = 0 := by
  exact planeBandContact_zero_iff_fibers ell hell planeWeakCos _ planeWeakCos_differentiable
    ((9999/10000 : ℝ)^4) (by positivity) (planeWeakCos_coercivity ell) N x
end VortexGap.Fermion

