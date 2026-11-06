import VortexGap.Fermion.CountableFrameMoments
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped BigOperators InnerProduct ComplexOrder

theorem countableFramePair_positive {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (u v : ι → CountableOrbital) :
    (countableFramePair Finset.univ (fun i => (w i : ℂ)) u v).IsPositive := by
  change (∑ i, (w i : ℂ) • InnerProductSpace.rankOne ℂ
    (countableWedge (u i) (v i)) (countableWedge (u i) (v i))).IsPositive
  rw [← countableScalarPairSynthesis_gram w hw (fun i => countableWedge (u i) (v i))]
  simpa only [ContinuousLinearMap.adjoint_adjoint] using
    ContinuousLinearMap.isPositive_adjoint_comp_self
      (countableScalarPairSynthesis w (fun i => countableWedge (u i) (v i))).adjoint

theorem countablePairConjugate_positive (J : CountableOrbital →ₗᵢ[ℂ] CountableOrbital)
    (Q : CountablePairSpace →L[ℂ] CountablePairSpace) (hQ : Q.IsPositive) :
    (countablePairConjugate J Q).IsPositive := by
  have h := hQ.adjoint_conj (countablePairMap J).adjoint
  simpa only [countablePairConjugate, ContinuousLinearMap.adjoint_adjoint,
    ContinuousLinearMap.comp_assoc] using h
end VortexGap.Fermion
