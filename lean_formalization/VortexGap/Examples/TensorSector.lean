import VortexGap.Fermion.TensorSector
import VortexGap.Examples.PairBounds

noncomputable section
set_option autoImplicit false
namespace VortexGap.Examples
open VortexGap.Fermion OAI.LaughlinGap.Occupation
open scoped InnerProduct

def threeParticleTensor : TensorSpace 5 3 :=
  sectorTensorIsometry 5 3 ⟨threeParticleState, threeParticleState_sector⟩

theorem threeParticleTensor_norm_sq : ‖threeParticleTensor‖ ^ 2 = 1 := by
  change ‖normalizedReadout 5 3 threeParticleState‖ ^ 2 = 1
  rw [tensorReadout_norm_sq threeParticleState_sector,
    norm_sq_eq_re_inner (𝕜 := ℂ), threeParticleState_inner]
  simp

theorem threeParticleTensor_coefficient :
    threeParticleTensor ![0, 1, 2] = (Real.sqrt 6 : ℂ)⁻¹ * (3 / 5 : ℂ) := by
  change normalizedReadout 5 3 threeParticleState ![0, 1, 2] = _
  rw [normalizedReadout_apply]
  have hf : List.ofFn ![(0 : Fin 5), 1, 2] = [0, 1, 2] := by decide
  have hne : ({0, 1, 2} : Finset (Fin 5)) ≠ {0, 3, 4} := by decide
  rw [hf, word_apply_empty_sorted _ (by decide)]
  norm_num [threeParticleState, ket, PiLp.single_apply, hne]

theorem threeParticleTensor_swap :
    threeParticleTensor (![0, 1, 2] ∘ Equiv.swap 0 1) =
      -(Real.sqrt 6 : ℂ)⁻¹ * (3 / 5 : ℂ) := by
  have h := tensorReadout_antisymmetric (N := 3) threeParticleState
  have hs := h 0 1 (by decide) ![0, 1, 2]
  change threeParticleTensor _ = -threeParticleTensor _ at hs
  rw [hs, threeParticleTensor_coefficient, neg_mul]

def zeroModeVacuum : particleSector 0 0 :=
  ⟨ket ∅, by
    change InSector 0 (ket (∅ : Finset (Fin 0)))
    simpa using (sector_ket (∅ : Finset (Fin 0)))⟩

theorem zeroModeVacuum_tensor (a : Fin 0 → Fin 0) :
    (sectorTensorIsometry 0 0 zeroModeVacuum : TensorSpace 0 0) a = 1 := by
  rw [sectorTensorIsometry_apply]
  simp [zeroModeVacuum, word_nil, ket]

end VortexGap.Examples
