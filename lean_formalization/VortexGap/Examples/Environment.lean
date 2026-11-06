import VortexGap.Fermion.Spectator
import VortexGap.Examples.FinitePairs

noncomputable section
set_option autoImplicit false
namespace VortexGap.Examples
open VortexGap.Fermion OAI.LaughlinGap.Occupation
open scoped InnerProduct

theorem system_creation_parity :
    fockSplit 1 1 (createMode 1 (ket {0})) ({0},{0}) = -1 := by
  have hj : joinOccupation ({0} : Finset (Fin 1)) (∅ : Finset (Fin 1)) = {0} := by decide
  change fockSplit 1 1 (transition (Fin.natAdd 1 (0 : Fin 1)) true (ket {0})) ({0},{0}) = _
  rw [fockSplit_transition_sys]
  norm_num [sign, OAI.LaughlinGap.Occupation.flip, fockSplit_apply, hj, ket]

theorem environment_creation_sign :
    fockSplit 1 1 (createMode 0 (ket {1})) ({0},{0}) = 1 := by
  have hj : joinOccupation (∅ : Finset (Fin 1)) ({0} : Finset (Fin 1)) = {1} := by decide
  change fockSplit 1 1 (transition (Fin.castAdd 1 (0 : Fin 1)) true (ket {1})) ({0},{0}) = _
  rw [fockSplit_transition_env]
  norm_num [sign, OAI.LaughlinGap.Occupation.flip, fockSplit_apply, hj, ket]

/-- Total degree two, with reference degrees two, one and zero. -/
def spectatorTestState : Space 4 :=
  ket {0,1} + Complex.I • ket {0,2} + (2 : ℂ) • ket {2,3}

theorem spectatorTestState_sector : InSector 2 spectatorTestState := by
  apply sector_add
  · apply sector_add
    · exact (by convert sector_ket ({0,1} : Finset (Fin 4)) using 1; norm_num)
    · apply sector_smul
      exact (by convert sector_ket ({0,2} : Finset (Fin 4)) using 1; norm_num)
  · apply sector_smul
    exact (by convert sector_ket ({2,3} : Finset (Fin 4)) using 1; norm_num)

theorem spectatorTestState_split :
    fockSplit 2 2 spectatorTestState =
      PiLp.single 2 ({0,1},∅) 1 + Complex.I • PiLp.single 2 ({0},{0}) 1 +
        (2 : ℂ) • PiLp.single 2 (∅,{0,1}) 1 := by
  have h01 : joinOccupation ({0,1} : Finset (Fin 2)) (∅ : Finset (Fin 2)) = {0,1} := by decide
  have h02 : joinOccupation ({0} : Finset (Fin 2)) ({0} : Finset (Fin 2)) = {0,2} := by decide
  have h23 : joinOccupation (∅ : Finset (Fin 2)) ({0,1} : Finset (Fin 2)) = {2,3} := by decide
  simp only [spectatorTestState, map_add, map_smul]
  rw [← h01, ← h02, ← h23, fockSplit_ket, fockSplit_ket, fockSplit_ket]

theorem spectatorTestState_ref_two :
    referenceSlice (∅ : Finset (Fin 2)) (fockSplit 2 2 spectatorTestState) = ket {0,1} := by
  ext A
  rw [referenceSlice_apply, spectatorTestState_split]
  simp [ket, PiLp.single_apply]

theorem spectatorTestState_ref_one :
    referenceSlice ({0} : Finset (Fin 2)) (fockSplit 2 2 spectatorTestState) =
      Complex.I • ket {0} := by
  ext A
  rw [referenceSlice_apply, spectatorTestState_split]
  simp [ket, PiLp.single_apply, show ({0} : Finset (Fin 2)) ≠ {0,1} by decide]

theorem spectatorTestState_ref_zero :
    referenceSlice ({0,1} : Finset (Fin 2)) (fockSplit 2 2 spectatorTestState) = (2 : ℂ) • ket ∅ := by
  ext A
  rw [referenceSlice_apply, spectatorTestState_split]
  simp [ket, PiLp.single_apply, show ({0,1} : Finset (Fin 2)) ≠ {0} by decide]

theorem environmentVacuum_mixedPair_norm_sq :
    ‖environmentVacuum 2 4 (pairEmbed mixedPair)‖ ^ 2 = 1 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), environmentVacuum_inner, pairEmbed_inner, mixedPair_inner]
  simp

end VortexGap.Examples
