import VortexGap.Fermion.FiniteOrbitals

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped InnerProduct ComplexConjugate

/-- Continuous extension in the actual one-particle l2 norm, with operator-norm codomain. -/
def countableCreate : CountableOrbital →L[ℂ] (CountableSpace →L[ℂ] CountableSpace) :=
  finiteOrbitalCreate.extendOfNorm orbitalEmbed

/-- Annihilation is the genuine Hilbert adjoint, hence antilinear in the orbital. -/
def countableAnnihilate (v : CountableOrbital) : CountableSpace →L[ℂ] CountableSpace :=
  (countableCreate v).adjoint

theorem countableCreate_embed (v : ℕ →₀ ℂ) :
    countableCreate (orbitalEmbed v) = finiteOrbitalCreate v := by
  exact LinearMap.extendOfNorm_eq orbitalEmbed_dense
    ⟨1, fun w => by simpa only [one_mul] using finiteOrbitalCreate_opNorm_le w⟩ v

theorem countableAnnihilate_embed (v : ℕ →₀ ℂ) :
    countableAnnihilate (orbitalEmbed v) = finiteOrbitalAnnihilate v := by
  simp only [countableAnnihilate, countableCreate_embed, finiteOrbitalAnnihilate]

theorem countableCreate_opNorm_le (v : CountableOrbital) : ‖countableCreate v‖ ≤ ‖v‖ := by
  exact (show ‖countableCreate v‖ ≤ 1 * ‖v‖ from
    LinearMap.norm_extendOfNorm_apply_le orbitalEmbed_dense 1
      (fun w => by simpa only [one_mul] using finiteOrbitalCreate_opNorm_le w) v).trans_eq (one_mul _)

theorem countableAnnihilate_opNorm_le (v : CountableOrbital) : ‖countableAnnihilate v‖ ≤ ‖v‖ := by
  calc
    _ = ‖countableCreate v‖ := ContinuousLinearMap.adjoint.norm_map _
    _ ≤ _ := countableCreate_opNorm_le v

theorem countableCreate_norm_le (v : CountableOrbital) (x : CountableSpace) :
    ‖countableCreate v x‖ ≤ ‖v‖ * ‖x‖ :=
  ((countableCreate v).le_opNorm x).trans
    (mul_le_mul_of_nonneg_right (countableCreate_opNorm_le v) (norm_nonneg x))

theorem countableAnnihilate_norm_le (v : CountableOrbital) (x : CountableSpace) :
    ‖countableAnnihilate v x‖ ≤ ‖v‖ * ‖x‖ :=
  ((countableAnnihilate v).le_opNorm x).trans
    (mul_le_mul_of_nonneg_right (countableAnnihilate_opNorm_le v) (norm_nonneg x))

theorem countableCreate_single (j : ℕ) (z : ℂ) :
    countableCreate (lp.single 2 j z) = z • countableCreateMode j := by
  rw [← orbitalEmbed_single, countableCreate_embed, finiteOrbitalCreate_single]

theorem countableAnnihilate_single (j : ℕ) (z : ℂ) :
    countableAnnihilate (lp.single 2 j z) = conj z • countableAnnihilateMode j := by
  rw [← orbitalEmbed_single, countableAnnihilate_embed, finiteOrbitalAnnihilate_single]

theorem countableCreate_ket (j : ℕ) : countableCreate (orbitalKet j) = countableCreateMode j := by
  simpa only [orbitalKet, one_smul] using countableCreate_single j 1

theorem countableAnnihilate_ket (j : ℕ) : countableAnnihilate (orbitalKet j) = countableAnnihilateMode j := by
  simpa only [orbitalKet, map_one, one_smul] using countableAnnihilate_single j 1

theorem countableAnnihilate_add (v w : CountableOrbital) :
    countableAnnihilate (v + w) = countableAnnihilate v + countableAnnihilate w := by
  simp only [countableAnnihilate, map_add]

theorem countableAnnihilate_smul (z : ℂ) (v : CountableOrbital) :
    countableAnnihilate (z • v) = conj z • countableAnnihilate v := by
  simp [countableAnnihilate, map_smulₛₗ]

theorem countableAnnihilate_adjoint (v : CountableOrbital) :
    (countableAnnihilate v).adjoint = countableCreate v :=
  ContinuousLinearMap.adjoint_adjoint _

@[fun_prop]
theorem countableAnnihilate_continuous : Continuous countableAnnihilate :=
  ContinuousLinearMap.adjoint.continuous.comp countableCreate.continuous

end VortexGap.Fermion
