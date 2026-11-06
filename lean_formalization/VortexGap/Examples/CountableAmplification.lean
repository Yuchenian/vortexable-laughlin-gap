import VortexGap.Operator.L2Amplification
import VortexGap.Fermion.CountableSplitOrbitals
import VortexGap.Examples.CountableSplitExamples

noncomputable section
set_option autoImplicit false
namespace VortexGap.Examples
open Fermion
open scoped ENNReal InnerProduct

/-- One environment particle and a genuinely infinite-support system orbital. -/
def amplificationGeometricState : CountableSplitSpace :=
  (l2Curry (Finset ℕ) (Finset ℕ)).symm (lp.single 2 {0} geometricOneParticle)

theorem amplificationGeometricState_norm_sq :
    ‖amplificationGeometricState‖ ^ 2 = (4/3 : ℝ) := by
  rw [amplificationGeometricState, LinearIsometryEquiv.norm_map,
    lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2), geometricOneParticle_norm_sq]

theorem amplificationGeometricState_coefficient (j : ℕ) :
    amplificationGeometricState ({0},{j}) = (Complex.I/2 : ℂ)^j := by
  change (lp.single 2 {0} geometricOneParticle : L2Matrix (Finset ℕ) (Finset ℕ)) {0} {j} = _
  simp only [lp.single_apply, Pi.single_eq_same]
  rw [geometricOneParticle, createVacuum_singleton_coefficient, geometricOrbital_coefficient]

theorem amplificationGeometricState_infinite_support (j : ℕ) :
    amplificationGeometricState ({0},{j}) ≠ 0 := by
  rw [amplificationGeometricState_coefficient]
  exact pow_ne_zero _ (by norm_num)

theorem amplificationGeometricState_sector :
    amplificationGeometricState ∈ countableSplitSector 2 := by
  intro AB hAB
  change (lp.single 2 {0} geometricOneParticle : L2Matrix (Finset ℕ) (Finset ℕ)) AB.1 AB.2 = 0
  by_cases h : ({0} : Finset ℕ) = AB.1
  · rw [← h]
    simp only [lp.single_apply, Pi.single_eq_same]
    apply geometricOneParticle_sector
    intro hc
    apply hAB
    rw [← h, Finset.card_singleton, hc]
  · simp [lp.single_apply, h]

/-- Ordinary system amplification has no graded sign; the physical odd system field
will additionally carry environment parity. This regression distinguishes the two. -/
theorem amplificationGeometricState_imaginary_annihilation :
    l2Amplify (Finset ℕ) (countableAnnihilate (Complex.I • geometricOrbital))
      amplificationGeometricState =
      ((-4/3 : ℂ) * Complex.I) • countableSplitKet ({0},∅) := by
  rw [amplificationGeometricState, l2Amplify_single_row, geometric_imaginary_annihilation]
  apply (l2Curry (Finset ℕ) (Finset ℕ)).injective
  rw [LinearIsometryEquiv.apply_symm_apply, map_smul, countableSplitKet, l2Curry_single]
  simp only [lp.single_smul, one_smul]
  rfl

theorem amplificationGeometricState_environment_number :
    countableEnvironmentProjection 1 amplificationGeometricState = amplificationGeometricState := by
  ext AB
  rw [countableEnvironmentProjection_apply]
  by_cases h : ({0} : Finset ℕ) = AB.1
  · rw [← h]; simp
  · have hz : amplificationGeometricState AB = 0 := by
      change (lp.single 2 {0} geometricOneParticle : L2Matrix (Finset ℕ) (Finset ℕ)) AB.1 AB.2 = 0
      simp [lp.single_apply, h]
    simp [hz]

theorem embeddedGeometric_env_coefficient (j : ℕ) :
    countableEnvOrbital geometricOrbital (Equiv.natSumNatEquivNat (Sum.inl j)) =
      (Complex.I/2 : ℂ)^j := by
  rw [countableEnvOrbital_env_coordinate, geometricOrbital_coefficient]

theorem embeddedGeometric_sys_coefficient (j : ℕ) :
    countableSysOrbital geometricOrbital (Equiv.natSumNatEquivNat (Sum.inr j)) =
      (Complex.I/2 : ℂ)^j := by
  rw [countableSysOrbital_sys_coordinate, geometricOrbital_coefficient]

theorem embeddedGeometric_orthogonal :
    inner ℂ (countableEnvOrbital geometricOrbital) (countableSysOrbital geometricOrbital) = 0 :=
  countableEnvSysOrbital_orthogonal _ _

theorem embeddedGeometric_env_norm_sq :
    ‖countableEnvOrbital geometricOrbital‖ ^ 2 = (4/3 : ℝ) := by
  rw [countableEnvOrbital_norm, geometricOrbital_norm_sq]

theorem embeddedGeometric_sys_norm_sq :
    ‖countableSysOrbital geometricOrbital‖ ^ 2 = (4/3 : ℝ) := by
  rw [countableSysOrbital_norm, geometricOrbital_norm_sq]

end VortexGap.Examples
