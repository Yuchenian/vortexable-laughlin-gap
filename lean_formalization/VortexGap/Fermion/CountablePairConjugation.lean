import VortexGap.Fermion.CountablePairTruncation
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open Filter
open scoped InnerProduct BigOperators Topology

def countablePairConjugate (J : CountableOrbital →ₗᵢ[ℂ] CountableOrbital)
    (Q : CountablePairSpace →L[ℂ] CountablePairSpace) :
    CountablePairSpace →L[ℂ] CountablePairSpace :=
  (countablePairMap J).comp (Q.comp (countablePairMap J).adjoint)

theorem countablePairConjugate_rankOne (J : CountableOrbital →ₗᵢ[ℂ] CountableOrbital)
    (p q : CountablePairSpace) :
    countablePairConjugate J (InnerProductSpace.rankOne ℂ p q) =
      InnerProductSpace.rankOne ℂ (countablePairMap J p) (countablePairMap J q) := by
  simp only [countablePairConjugate, InnerProductSpace.rankOne_comp,
    ContinuousLinearMap.adjoint_adjoint, InnerProductSpace.comp_rankOne]

theorem countablePairConjugate_sum (J : CountableOrbital →ₗᵢ[ℂ] CountableOrbital)
    {ι : Type*} (s : Finset ι) (Q : ι → CountablePairSpace →L[ℂ] CountablePairSpace) :
    countablePairConjugate J (∑ a ∈ s, Q a) = ∑ a ∈ s, countablePairConjugate J (Q a) := by
  ext p
  simp [countablePairConjugate, map_sum]

theorem countablePairConjugate_norm_le (J : CountableOrbital →ₗᵢ[ℂ] CountableOrbital)
    (Q : CountablePairSpace →L[ℂ] CountablePairSpace) :
    ‖countablePairConjugate J Q‖ ≤ ‖Q‖ := by
  have h : ‖countablePairMap J‖ ≤ 1 :=
    (countablePairIsometry J).norm_toContinuousLinearMap_le
  have ha : ‖(countablePairMap J).adjoint‖ ≤ 1 := by
    rwa [ContinuousLinearMap.adjoint.norm_map]
  unfold countablePairConjugate
  calc
    _ ≤ ‖countablePairMap J‖ * ‖Q.comp (countablePairMap J).adjoint‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * (‖Q‖ * 1) := mul_le_mul h
      ((ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left ha (norm_nonneg Q))) (norm_nonneg _) (by norm_num)
    _ = ‖Q‖ := by ring

theorem countablePairConjugate_tendsto
    (J : CountableOrbital →ₗᵢ[ℂ] CountableOrbital)
    {ι : Type*} {l : Filter ι}
    (Q : ι → CountablePairSpace →L[ℂ] CountablePairSpace)
    (R : CountablePairSpace →L[ℂ] CountablePairSpace)
    (h : ∀ p, Tendsto (fun i => Q i p) l (𝓝 (R p))) (p : CountablePairSpace) :
    Tendsto (fun i => countablePairConjugate J (Q i) p) l
      (𝓝 (countablePairConjugate J R p)) :=
  (countablePairMap J).continuous.continuousAt.tendsto.comp
    (h ((countablePairMap J).adjoint p))
end VortexGap.Fermion
