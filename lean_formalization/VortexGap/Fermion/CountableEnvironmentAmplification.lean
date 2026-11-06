import VortexGap.Fermion.CountableSplitParity
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion

/-- Ordinary tensor-coordinate swap, not the graded Fock swap. -/
def countableSplitExchange : CountableSplitSpace ≃ₗᵢ[ℂ] CountableSplitSpace :=
  (l2Curry (Finset ℕ) (Finset ℕ)).trans
    ((l2Exchange (Finset ℕ) (Finset ℕ)).trans (l2Curry (Finset ℕ) (Finset ℕ)).symm)

theorem countableSplitExchange_apply (x : CountableSplitSpace) (A B : Finset ℕ) :
    countableSplitExchange x (A,B) = x (B,A) := rfl

theorem countableSplitExchange_involutive (x : CountableSplitSpace) :
    countableSplitExchange (countableSplitExchange x) = x := by ext AB; rfl

def countableEnvironmentFiber (x : CountableSplitSpace) (B : Finset ℕ) : CountableSpace :=
  l2ProductFiber (countableSplitExchange x) B

theorem countableEnvironmentFiber_apply (x : CountableSplitSpace) (A B : Finset ℕ) :
    countableEnvironmentFiber x B A = x (A,B) := rfl

def countableEnvironmentAmplify (Q : CountableSpace →L[ℂ] CountableSpace) :
    CountableSplitSpace →L[ℂ] CountableSplitSpace :=
  countableSplitExchange.toLinearIsometry.toContinuousLinearMap.comp
    ((l2Amplify (Finset ℕ) Q).comp countableSplitExchange.toLinearIsometry.toContinuousLinearMap)

theorem countableEnvironmentAmplify_apply (Q : CountableSpace →L[ℂ] CountableSpace)
    (x : CountableSplitSpace) (A B : Finset ℕ) :
    countableEnvironmentAmplify Q x (A,B) = Q (countableEnvironmentFiber x B) A := rfl

theorem countableEnvironmentAmplify_norm_le (Q : CountableSpace →L[ℂ] CountableSpace)
    (x : CountableSplitSpace) : ‖countableEnvironmentAmplify Q x‖ ≤ ‖Q‖ * ‖x‖ := by
  change ‖countableSplitExchange (l2Amplify (Finset ℕ) Q (countableSplitExchange x))‖ ≤ _
  rw [countableSplitExchange.norm_map]
  exact (l2Amplify_norm_le Q (countableSplitExchange x)).trans_eq
    (congrArg (fun t => ‖Q‖ * t) (countableSplitExchange.norm_map x))

theorem countableEnvironmentAmplify_fiber (Q : CountableSpace →L[ℂ] CountableSpace)
    (x : CountableSplitSpace) (B : Finset ℕ) :
    countableEnvironmentFiber (countableEnvironmentAmplify Q x) B =
      Q (countableEnvironmentFiber x B) := by ext A; rfl

theorem countableSplit_create_env_fiber (j : ℕ) (x : CountableSplitSpace) (B : Finset ℕ) :
    countableEnvironmentFiber (countableSplitConjugate (countableCreate (countableEnvBasis j)) x) B =
      countableCreateMode j (countableEnvironmentFiber x B) := by
  ext A
  change countableSplitConjugate (countableCreate (countableEnvBasis j)) x (A,B) =
    countableCreateMode j (countableEnvironmentFiber x B) A
  rw [countableSplit_create_env_coordinate, countableTransition_apply]
  by_cases h : j ∈ A
  · simp [h, countableFlip_of_mem h, countableEnvironmentFiber_apply]
  · simp [h]

theorem countableSplit_annihilate_env_fiber (j : ℕ) (x : CountableSplitSpace) (B : Finset ℕ) :
    countableEnvironmentFiber (countableSplitConjugate (countableAnnihilate (countableEnvBasis j)) x) B =
      countableAnnihilateMode j (countableEnvironmentFiber x B) := by
  ext A
  change countableSplitConjugate (countableAnnihilate (countableEnvBasis j)) x (A,B) =
    countableAnnihilateMode j (countableEnvironmentFiber x B) A
  rw [countableSplit_annihilate_env_coordinate, countableTransition_apply]
  by_cases h : j ∈ A
  · simp [h]
  · simp [h, countableFlip_of_not_mem h, countableEnvironmentFiber_apply]
end VortexGap.Fermion
