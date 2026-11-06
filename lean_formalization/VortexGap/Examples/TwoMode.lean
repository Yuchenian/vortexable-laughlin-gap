import VortexGap.Fermion.Finite

noncomputable section
set_option autoImplicit false
namespace VortexGap.Examples
open VortexGap.Fermion OAI.LaughlinGap.Occupation
open scoped ComplexConjugate

/-- Unit-normalized ordered two-particle state: no extra factor of two. -/
theorem two_mode_pair :
    (annihilateMode (1 : Fin 2) * annihilateMode (0 : Fin 2)) (ket {0, 1}) = ket ∅ := by
  ext A
  fin_cases A <;>
    norm_num [annihilateMode, annihilation, Module.End.mul_apply, transition_apply,
      ket, OAI.LaughlinGap.Occupation.flip, sign, Finset.filter_insert] <;> decide

theorem two_mode_reversed :
    (annihilateMode (0 : Fin 2) * annihilateMode (1 : Fin 2)) (ket {0, 1}) = -ket ∅ := by
  rw [mode_anticommute]
  simpa using congrArg Neg.neg two_mode_pair

/-- Both the pair wavefunction and its annihilator carry a non-real phase.
Omitting the conjugation in B(p) would give the wrong sign in this test. -/
theorem two_mode_complex_phase :
    (conj Complex.I • (annihilateMode (1 : Fin 2) * annihilateMode (0 : Fin 2)))
      (Complex.I • ket {0, 1}) = ket ∅ := by
  simp only [LinearMap.smul_apply, map_smul, two_mode_pair, smul_smul]
  simp

theorem two_mode_unit_norm : ‖(ket {0, 1} : Space 2)‖ = 1 := ket_norm _

end VortexGap.Examples
