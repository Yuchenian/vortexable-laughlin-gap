import VortexGap.Fermion.CountableOrbitalOperators

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped BigOperators InnerProduct ComplexConjugate

theorem finiteOrbitalCreate_anticommute (v w : ℕ →₀ ℂ) :
    finiteOrbitalCreate v * finiteOrbitalCreate w =
      -(finiteOrbitalCreate w * finiteOrbitalCreate v) := by
  have hm (i : ℕ) : countableCreateMode i * finiteOrbitalCreate w =
      -(finiteOrbitalCreate w * countableCreateMode i) := by
    rw [finiteOrbitalCreate_sum w]
    simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc,
      ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [countableTransition_anticommute i j true]
    exact smul_neg (w j) (countableCreateMode j * countableCreateMode i)
  rw [finiteOrbitalCreate_sum v]
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hm]
  exact smul_neg (v i) (finiteOrbitalCreate w * countableCreateMode i)

/-- Mixed CAR for every square-summable complex orbital, as a bounded-operator identity. -/
theorem countableOrbital_car (v w : CountableOrbital) :
    countableAnnihilate v * countableCreate w + countableCreate w * countableAnnihilate v =
      (inner ℂ v w) • 1 := by
  refine orbitalEmbed_dense.induction_on₂ ?_ ?_ v w
  · apply isClosed_eq <;> fun_prop
  · intro a b
    simpa only [countableAnnihilate_embed, countableCreate_embed] using finiteOrbital_car a b

theorem countableCreate_anticommute (v w : CountableOrbital) :
    countableCreate v * countableCreate w = -(countableCreate w * countableCreate v) := by
  refine orbitalEmbed_dense.induction_on₂ ?_ ?_ v w
  · apply isClosed_eq <;> fun_prop
  · intro a b
    simpa only [countableCreate_embed] using finiteOrbitalCreate_anticommute a b

theorem countableAnnihilate_anticommute (v w : CountableOrbital) :
    countableAnnihilate v * countableAnnihilate w =
      -(countableAnnihilate w * countableAnnihilate v) := by
  have h := congrArg (fun T : CountableSpace →L[ℂ] CountableSpace => T.adjoint)
    (countableCreate_anticommute w v)
  change ((countableCreate w).comp (countableCreate v)).adjoint =
    (-((countableCreate v).comp (countableCreate w))).adjoint at h
  rw [map_neg, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp] at h
  ext x A
  exact congrArg (fun T : CountableSpace →L[ℂ] CountableSpace => T x A) h

theorem countableCreate_square (v : CountableOrbital) : countableCreate v * countableCreate v = 0 := by
  ext x A
  have h := congrArg (fun T : CountableSpace →L[ℂ] CountableSpace => T x A)
    (countableCreate_anticommute v v)
  change countableCreate v (countableCreate v x) A =
    -(countableCreate v (countableCreate v x) A) at h
  change countableCreate v (countableCreate v x) A = 0
  linear_combination (1 / 2 : ℂ) * h

theorem countableAnnihilate_square (v : CountableOrbital) :
    countableAnnihilate v * countableAnnihilate v = 0 := by
  ext x A
  have h := congrArg (fun T : CountableSpace →L[ℂ] CountableSpace => T x A)
    (countableAnnihilate_anticommute v v)
  change countableAnnihilate v (countableAnnihilate v x) A =
    -(countableAnnihilate v (countableAnnihilate v x) A) at h
  change countableAnnihilate v (countableAnnihilate v x) A = 0
  linear_combination (1 / 2 : ℂ) * h

theorem countableOrbital_norm_identity (v : CountableOrbital) (x : CountableSpace) :
    ‖countableCreate v x‖ ^ 2 + ‖countableAnnihilate v x‖ ^ 2 = ‖v‖ ^ 2 * ‖x‖ ^ 2 := by
  refine orbitalEmbed_dense.induction_on v ?_ ?_
  · apply isClosed_eq <;> fun_prop
  · intro a
    simpa only [countableCreate_embed, countableAnnihilate_embed] using finiteOrbital_norm_identity a x

end VortexGap.Fermion
