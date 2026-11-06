import VortexGap.Physical.PlaneZeroModes
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped InnerProduct ComplexOrder BoundedContinuousFunction

/-- A one-sided orbital inverse lifts to the completed exterior square. -/
theorem countablePairFilter_cancel
    (S R : CountableOrbital →L[ℂ] CountableOrbital) (hS : 0 ≤ S) (hR : 0 ≤ R)
    (hinv : S * R = 1) (p : CountablePairSpace) :
    countablePairFilter S hS (countablePairFilter R hR p) = p := by
  have h (x : CountableOrbital) : S (R x) = x :=
    congrArg (fun T : CountableOrbital →L[ℂ] CountableOrbital => T x) hinv
  have hop : (countablePairFilter S hS).comp (countablePairFilter R hR) = 1 := by
    apply countablePairOperator_ext_wedge
    intro u v
    simp only [ContinuousLinearMap.comp_apply, countablePairFilter_wedge, h]
    rfl
  exact congrArg (fun T : CountablePairSpace →L[ℂ] CountablePairSpace => T p) hop

def gramRoot {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (F : H →L[ℂ] K) := CFC.sqrt (gramOperator F)

theorem gramRoot_nonneg {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (F : H →L[ℂ] K) : 0 ≤ gramRoot F := CFC.sqrt_nonneg _

/-- In normalized pair coordinates the deformed kernel is the image of the
reference kernel under the exterior square of the positive Gram square root. -/
theorem planeBandContact_two_zero_iff_image (ell : ℝ) (hell : 0 < ell) (f : ℂ →ᵇ ℂ)
    (hG : IsStrictlyPositive (planeScalarGram ell hell f)) (hf : Differentiable ℝ f)
    (κ : ℝ) (hκ : 0 < κ) (hw : (κ : ℂ) • planePairOperator ≤ planeWeightedPairOperator ell f)
    (p : CountablePairSpace) :
    planeBandContactOperator ell hell f hG hf 2
      ⟨countablePairEmbedding p, countablePairEmbedding_sector p⟩ = 0 ↔
    ∃ q : CountablePairSpace, planePairOperator q = 0 ∧
      countablePairFilter (gramRoot (planeScalarEmbedding ell hell f)) (gramRoot_nonneg _) q = p := by
  rw [planeBandContact_two_zero_iff ell hell f hG hf κ hκ hw]
  let F := planeScalarEmbedding ell hell f
  let R := gramInvSqrt F
  let S := gramRoot F
  have hR : 0 ≤ R := gramInvSqrt_nonneg F hG
  have hS : 0 ≤ S := gramRoot_nonneg F
  constructor
  · intro hz
    exact ⟨countablePairFilter R hR p, hz,
      countablePairFilter_cancel S R hS hR (gramInvSqrt_right F hG) p⟩
  · rintro ⟨q, hz, rfl⟩
    change planePairOperator (countablePairFilter R hR (countablePairFilter S hS q)) = 0
    rwa [countablePairFilter_cancel R S hR hS (gramInvSqrt_left F hG)]
end VortexGap.Fermion

