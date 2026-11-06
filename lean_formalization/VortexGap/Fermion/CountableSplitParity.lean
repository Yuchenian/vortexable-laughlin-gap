import VortexGap.Fermion.CountableSplitOrbitalFields
import VortexGap.Fermion.CountableEnvironmentProjection
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped InnerProduct ComplexConjugate

def countableEnvironmentParityLinear : CountableSplitSpace →ₗ[ℂ] CountableSplitSpace where
  toFun x := ⟨fun AB => (-1 : ℂ)^AB.1.card * x AB,
    (lp.memℓp x).mono' (fun AB => by simp [norm_mul])⟩
  map_add' x y := by
    ext AB
    change (-1 : ℂ)^AB.1.card * (x AB + y AB) =
      (-1 : ℂ)^AB.1.card * x AB + (-1 : ℂ)^AB.1.card * y AB
    exact mul_add _ _ _
  map_smul' c x := by ext AB; simp [mul_left_comm]

theorem countableEnvironmentParityLinear_norm (x : CountableSplitSpace) :
    ‖countableEnvironmentParityLinear x‖ = ‖x‖ := by
  apply le_antisymm
  · apply lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0)
    intro AB
    change ‖(-1 : ℂ)^AB.1.card * x AB‖ ≤ ‖x AB‖
    simp [norm_mul]
  · apply lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0)
    intro AB
    change ‖x AB‖ ≤ ‖(-1 : ℂ)^AB.1.card * x AB‖
    simp [norm_mul]

def countableEnvironmentParity : CountableSplitSpace →L[ℂ] CountableSplitSpace :=
  countableEnvironmentParityLinear.mkContinuous 1 (fun x => by
    rw [countableEnvironmentParityLinear_norm, one_mul])

theorem countableEnvironmentParity_apply (x : CountableSplitSpace) (AB : Finset ℕ × Finset ℕ) :
    countableEnvironmentParity x AB = (-1 : ℂ)^AB.1.card * x AB := rfl

theorem countableEnvironmentParity_norm (x : CountableSplitSpace) :
    ‖countableEnvironmentParity x‖ = ‖x‖ := countableEnvironmentParityLinear_norm x

theorem countableEnvironmentParity_square :
    countableEnvironmentParity.comp countableEnvironmentParity = 1 := by
  ext x AB
  change (-1 : ℂ)^AB.1.card * ((-1 : ℂ)^AB.1.card * x AB) = x AB
  rw [← mul_assoc, ← mul_pow]
  norm_num

theorem countableEnvironmentParity_fiber (x : CountableSplitSpace) (A : Finset ℕ) :
    l2ProductFiber (countableEnvironmentParity x) A =
      ((-1 : ℂ)^A.card) • l2ProductFiber x A := by
  ext B; rfl

theorem countableEnvironmentParity_commute (Q : CountableSpace →L[ℂ] CountableSpace) :
    countableEnvironmentParity.comp (l2Amplify (Finset ℕ) Q) =
      (l2Amplify (Finset ℕ) Q).comp countableEnvironmentParity := by
  ext x AB
  change (-1 : ℂ)^AB.1.card * Q (l2ProductFiber x AB.1) AB.2 =
    Q (l2ProductFiber (countableEnvironmentParity x) AB.1) AB.2
  rw [countableEnvironmentParity_fiber, map_smul]
  rfl

theorem countableSplit_create_sys_tensor (v : CountableOrbital) :
    countableSplitConjugate (countableCreate (countableSysOrbital v)) =
      countableEnvironmentParity.comp (l2Amplify (Finset ℕ) (countableCreate v)) := by
  ext x AB
  exact countableSplit_create_sys_orbital_coordinate v x AB.1 AB.2

theorem countableSplit_annihilate_sys_tensor (v : CountableOrbital) :
    countableSplitConjugate (countableAnnihilate (countableSysOrbital v)) =
      countableEnvironmentParity.comp (l2Amplify (Finset ℕ) (countableAnnihilate v)) := by
  ext x AB
  exact countableSplit_annihilate_sys_orbital_coordinate v x AB.1 AB.2

end VortexGap.Fermion
