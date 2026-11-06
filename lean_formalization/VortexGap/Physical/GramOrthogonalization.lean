import VortexGap.Physical.FormComparison
noncomputable section
set_option autoImplicit false
namespace VortexGap
open scoped InnerProduct ComplexOrder
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def gramOperator (F : H →L[ℂ] K) : H →L[ℂ] H := F.adjoint.comp F

theorem gramOperator_nonneg (F : H →L[ℂ] K) : 0 ≤ gramOperator F :=
  ContinuousLinearMap.nonneg_iff_isPositive.mpr (ContinuousLinearMap.isPositive_adjoint_comp_self F)

theorem gramOperator_strict (F : H →L[ℂ] K) (g : ℝ) (hg : 0 < g)
    (hlo : g • (1 : H →L[ℂ] H) ≤ gramOperator F) : IsStrictlyPositive (gramOperator F) :=
  (IsStrictlyPositive.smul hg isStrictlyPositive_one).of_le hlo

def gramInvSqrt (F : H →L[ℂ] K) : H →L[ℂ] H := Ring.inverse (CFC.sqrt (gramOperator F))

theorem gramInvSqrt_nonneg (F : H →L[ℂ] K) (hF : IsStrictlyPositive (gramOperator F)) :
    0 ≤ gramInvSqrt F := hF.sqrt.ringInverse.nonneg

theorem gramInvSqrt_left (F : H →L[ℂ] K) (hF : IsStrictlyPositive (gramOperator F)) :
    gramInvSqrt F * CFC.sqrt (gramOperator F) = 1 :=
  Ring.inverse_mul_cancel _ hF.sqrt.isUnit

theorem gramInvSqrt_right (F : H →L[ℂ] K) (hF : IsStrictlyPositive (gramOperator F)) :
    CFC.sqrt (gramOperator F) * gramInvSqrt F = 1 :=
  Ring.mul_inverse_cancel _ hF.sqrt.isUnit

def gramNormalized (F : H →L[ℂ] K) : H →L[ℂ] K := F.comp (gramInvSqrt F)

theorem gramNormalized_inner (F : H →L[ℂ] K) (hF : IsStrictlyPositive (gramOperator F))
    (x y : H) : inner ℂ (gramNormalized F x) (gramNormalized F y) = inner ℂ x y := by
  let S := CFC.sqrt (gramOperator F)
  have hs : S.adjoint = S := (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)).star_eq
  have hxy (u v : H) : inner ℂ (F u) (F v) = inner ℂ (S u) (S v) := by
    rw [← ContinuousLinearMap.adjoint_inner_right F,
      ← ContinuousLinearMap.adjoint_inner_right S, hs]
    change inner ℂ u (gramOperator F v) = inner ℂ u ((S*S) v)
    rw [show S*S = gramOperator F from CFC.sqrt_mul_sqrt_self _ (gramOperator_nonneg F)]
  change inner ℂ (F (gramInvSqrt F x)) (F (gramInvSqrt F y)) = _
  rw [hxy]
  have hi (z : H) : S (gramInvSqrt F z) = z :=
    congrArg (fun T : H →L[ℂ] H => T z) (gramInvSqrt_right F hF)
  rw [hi, hi]

def gramIsometry (F : H →L[ℂ] K) (hF : IsStrictlyPositive (gramOperator F)) : H →ₗᵢ[ℂ] K :=
  (gramNormalized F).toLinearMap.isometryOfInner (gramNormalized_inner F hF)

theorem gramIsometry_range (F : H →L[ℂ] K) (hF : IsStrictlyPositive (gramOperator F)) :
    (gramIsometry F hF).toLinearMap.range = F.toLinearMap.range := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨gramInvSqrt F x, rfl⟩
  · rintro ⟨x, rfl⟩
    refine ⟨CFC.sqrt (gramOperator F) x, ?_⟩
    change F (gramInvSqrt F (CFC.sqrt (gramOperator F) x)) = F x
    have hi := congrArg (fun T : H →L[ℂ] H => T x) (gramInvSqrt_left F hF)
    exact congrArg F hi

/-- Constructed unitary onto the actual range of F. -/
def gramRangeUnitary (F : H →L[ℂ] K) (hF : IsStrictlyPositive (gramOperator F)) :
    H ≃ₗᵢ[ℂ] F.toLinearMap.range :=
  (gramIsometry F hF).equivRange.trans
    (LinearIsometryEquiv.ofEq _ _ (gramIsometry_range F hF))

theorem gramRangeUnitary_apply (F : H →L[ℂ] K) (hF : IsStrictlyPositive (gramOperator F))
    (x : H) : (gramRangeUnitary F hF x : K) = F (gramInvSqrt F x) := rfl

theorem gramRange_closed (F : H →L[ℂ] K) (hF : IsStrictlyPositive (gramOperator F)) :
    IsClosed (F.toLinearMap.range : Set K) := by
  rw [← gramIsometry_range F hF]
  exact (gramIsometry F hF).isometry.isClosedEmbedding.isClosed_range

theorem gramInvSqrt_eq_sqrt_inverse (F : H →L[ℂ] K) :
    gramInvSqrt F = CFC.sqrt (Ring.inverse (gramOperator F)) :=
  CFC.sqrt_ringInverse.symm

/-- The only invertibility input is the original strictly positive Gram lower bound. -/
theorem gram_orthogonalization (F : H →L[ℂ] K) (g : ℝ) (hg : 0 < g)
    (hlo : g • (1 : H →L[ℂ] H) ≤ gramOperator F) :
    IsClosed (F.toLinearMap.range : Set K) ∧
    ∃ U : H ≃ₗᵢ[ℂ] F.toLinearMap.range,
      ∀ x, (U x : K) = F (CFC.sqrt (Ring.inverse (gramOperator F)) x) := by
  have hF := gramOperator_strict F g hg hlo
  refine ⟨gramRange_closed F hF, gramRangeUnitary F hF, ?_⟩
  intro x
  rw [gramRangeUnitary_apply, gramInvSqrt_eq_sqrt_inverse]

end VortexGap
