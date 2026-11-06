import VortexGap.Fermion.CountableOrbitalCAR

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped BigOperators InnerProduct ComplexConjugate

/-- Unconditional convergence in operator norm, from square-summability of the orbital. -/
theorem countableCreate_hasSum (v : CountableOrbital) :
    HasSum (fun j => v j • countableCreateMode j) (countableCreate v) := by
  have h := (orbital_hasSum v).map countableCreate.toAddMonoidHom countableCreate.continuous
  change HasSum (fun j => countableCreate (v j • orbitalKet j)) (countableCreate v) at h
  simpa only [map_smul, countableCreate_ket] using h

theorem countableAnnihilate_hasSum (v : CountableOrbital) :
    HasSum (fun j => conj (v j) • countableAnnihilateMode j) (countableAnnihilate v) := by
  have h := (countableCreate_hasSum v).map ContinuousLinearMap.adjoint.toAddMonoidHom
    ContinuousLinearMap.adjoint.continuous
  change HasSum (fun j => (v j • countableCreateMode j).adjoint) (countableCreate v).adjoint at h
  simpa only [countableAnnihilate, map_smulₛₗ, countableTransition_adjoint, Bool.not_true, countableAnnihilateMode] using h

theorem countableCreate_sector {N : ℕ} (v : CountableOrbital) {x : CountableSpace}
    (hx : x ∈ countableSector N) : countableCreate v x ∈ countableSector (N + 1) := by
  refine orbitalEmbed_dense.induction_on v ?_ ?_
  · exact (countableSector_isClosed (N + 1)).preimage (by fun_prop)
  · intro a
    rw [countableCreate_embed, finiteOrbitalCreate_sum, ContinuousLinearMap.sum_apply]
    exact (countableSector (N + 1)).sum_mem fun j hj =>
      (countableSector (N + 1)).smul_mem (a j) (countableCreateMode_sector j hx)

theorem countableAnnihilate_sector {N : ℕ} (v : CountableOrbital) {x : CountableSpace}
    (hx : x ∈ countableSector (N + 1)) : countableAnnihilate v x ∈ countableSector N := by
  refine orbitalEmbed_dense.induction_on v ?_ ?_
  · exact (countableSector_isClosed N).preimage (by fun_prop)
  · intro a
    rw [countableAnnihilate_embed, finiteOrbitalAnnihilate_sum, ContinuousLinearMap.sum_apply]
    exact (countableSector N).sum_mem fun j hj =>
      (countableSector N).smul_mem (conj (a j)) (countableAnnihilateMode_sector j hx)

theorem countableAnnihilate_zero_sector (v : CountableOrbital) {x : CountableSpace}
    (hx : x ∈ countableSector 0) : countableAnnihilate v x = 0 := by
  refine orbitalEmbed_dense.induction_on v ?_ ?_
  · apply isClosed_eq <;> fun_prop
  · intro a
    rw [countableAnnihilate_embed, finiteOrbitalAnnihilate_sum, ContinuousLinearMap.sum_apply]
    apply Finset.sum_eq_zero
    intro j hj
    change conj (a j) • countableAnnihilateMode j x = 0
    rw [countableAnnihilateMode_zero_sector j hx]
    ext A
    change conj (a j) * (0 : ℂ) = 0
    exact mul_zero _

theorem countableAnnihilate_vacuum (v : CountableOrbital) :
    countableAnnihilate v (countableKet ∅) = 0 :=
  countableAnnihilate_zero_sector v (by simpa using countableKet_sector ∅)

theorem countableCreate_vacuum_norm (v : CountableOrbital) :
    ‖countableCreate v (countableKet ∅)‖ = ‖v‖ := by
  have h := countableOrbital_norm_identity v (countableKet ∅)
  simp [countableAnnihilate_vacuum, countableKet_norm] at h
  nlinarith [norm_nonneg (countableCreate v (countableKet ∅)), norm_nonneg v]

/-- Sharp induced norm on the full occupation space, not an arbitrary restricted sector. -/
theorem countableCreate_opNorm_eq (v : CountableOrbital) : ‖countableCreate v‖ = ‖v‖ := by
  apply le_antisymm (countableCreate_opNorm_le v)
  have h := (countableCreate v).le_opNorm (countableKet ∅)
  simpa only [countableCreate_vacuum_norm, countableKet_norm, mul_one] using h

theorem countableAnnihilate_opNorm_eq (v : CountableOrbital) : ‖countableAnnihilate v‖ = ‖v‖ := by
  calc
    _ = ‖countableCreate v‖ := ContinuousLinearMap.adjoint.norm_map _
    _ = _ := countableCreate_opNorm_eq v

theorem countableAnnihilate_create_vacuum (v w : CountableOrbital) :
    countableAnnihilate v (countableCreate w (countableKet ∅)) =
      (inner ℂ v w) • countableKet ∅ := by
  have h := congrArg (fun T : CountableSpace →L[ℂ] CountableSpace => T (countableKet ∅))
    (countableOrbital_car v w)
  change countableAnnihilate v (countableCreate w (countableKet ∅)) +
    countableCreate w (countableAnnihilate v (countableKet ∅)) =
      (inner ℂ v w) • countableKet ∅ at h
  simpa only [countableAnnihilate_vacuum, map_zero, add_zero] using h

end VortexGap.Fermion
