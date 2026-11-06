import VortexGap.Fermion.ExteriorPower
import VortexGap.Examples.TensorSector

/-! A nonidentity complex orbital phase changes relative amplitudes of a true
three-particle state. These are functor regressions, not gap-transfer instances. -/
noncomputable section
set_option autoImplicit false
namespace VortexGap.Examples
open VortexGap.Fermion OAI.LaughlinGap.Occupation
open scoped BigOperators InnerProduct

def phaseAt3 (i : Fin 5) : ℂ := if i = 3 then Complex.I else 1

def phaseMap : Module.End ℂ (EuclideanSpace ℂ (Fin 5)) where
  toFun x := WithLp.toLp 2 (fun i => phaseAt3 i * x i)
  map_add' x y := by ext i; exact mul_add _ _ _
  map_smul' z x := by ext i; exact mul_left_comm _ _ _

theorem phaseMap_norm (x : EuclideanSpace ℂ (Fin 5)) : ‖phaseMap x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i _
  change ‖phaseAt3 i * x i‖ ^ 2 = ‖x i‖ ^ 2
  have h : ‖phaseAt3 i‖ = 1 := by unfold phaseAt3; split_ifs <;> simp
  rw [norm_mul, h, one_mul]

def phaseIsometry : EuclideanSpace ℂ (Fin 5) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin 5) where
  toLinearMap := phaseMap
  norm_map' := phaseMap_norm

theorem phase_tensor_apply {N : ℕ} (ψ : TensorSpace 5 N) (a : Fin N → Fin 5) :
    tensorPower phaseMap N ψ a = (∏ i, phaseAt3 (a i)) * ψ a := by
  classical
  have hk (b : Fin N → Fin 5) : tensorKernel phaseMap a b =
      (∏ i, phaseAt3 (a i)) * tensorKernel (LinearMap.id : Module.End ℂ (EuclideanSpace ℂ (Fin 5))) a b := by
    change (∏ i, phaseAt3 (a i) *
      (PiLp.single 2 (b i) (1 : ℂ) : EuclideanSpace ℂ (Fin 5)) (a i)) = _
    exact Finset.prod_mul_distrib
  simp only [tensorPower_apply, hk, tensorKernel_id, mul_assoc, ← Finset.mul_sum]
  simp

theorem threeParticleTensor_other_coefficient :
    threeParticleTensor ![0, 3, 4] = (Real.sqrt 6 : ℂ)⁻¹ * (4 / 5 * Complex.I : ℂ) := by
  change normalizedReadout 5 3 threeParticleState ![0, 3, 4] = _
  rw [normalizedReadout_apply]
  have hf : List.ofFn ![(0 : Fin 5), 3, 4] = [0, 3, 4] := by decide
  have hne : ({0, 3, 4} : Finset (Fin 5)) ≠ {0, 1, 2} := by decide
  rw [hf, word_apply_empty_sorted _ (by decide)]
  norm_num [threeParticleState, ket, PiLp.single_apply, hne]

def phaseSectorImage : particleSector 5 3 :=
  exteriorPower phaseMap 3 ⟨threeParticleState, threeParticleState_sector⟩

theorem phaseSectorImage_norm_sq : ‖phaseSectorImage‖ ^ 2 = 1 := by
  change ‖exteriorPower phaseIsometry.toLinearMap 3
    ⟨threeParticleState, threeParticleState_sector⟩‖ ^ 2 = 1
  rw [exteriorPower_norm]
  change ‖threeParticleState‖ ^ 2 = 1
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), threeParticleState_inner]
  simp

theorem phaseSectorImage_first :
    (sectorTensorIsometry 5 3 phaseSectorImage : TensorSpace 5 3) ![0, 1, 2] =
      (Real.sqrt 6 : ℂ)⁻¹ * (3 / 5 : ℂ) := by
  have h := congrArg (fun ψ : antisymmetricTensors 5 3 =>
    (ψ : TensorSpace 5 3) ![0, 1, 2])
    (exteriorPower_tensor phaseMap 3 ⟨threeParticleState, threeParticleState_sector⟩)
  change (sectorTensorIsometry 5 3 phaseSectorImage : TensorSpace 5 3) ![0, 1, 2] =
    tensorPower phaseMap 3 threeParticleTensor ![0, 1, 2] at h
  rw [h, phase_tensor_apply, threeParticleTensor_coefficient]
  norm_num [Fin.prod_univ_succ, phaseAt3]

theorem phaseSectorImage_other :
    (sectorTensorIsometry 5 3 phaseSectorImage : TensorSpace 5 3) ![0, 3, 4] =
      (Real.sqrt 6 : ℂ)⁻¹ * (-4 / 5 : ℂ) := by
  have h := congrArg (fun ψ : antisymmetricTensors 5 3 =>
    (ψ : TensorSpace 5 3) ![0, 3, 4])
    (exteriorPower_tensor phaseMap 3 ⟨threeParticleState, threeParticleState_sector⟩)
  change (sectorTensorIsometry 5 3 phaseSectorImage : TensorSpace 5 3) ![0, 3, 4] =
    tensorPower phaseMap 3 threeParticleTensor ![0, 3, 4] at h
  rw [h, phase_tensor_apply, threeParticleTensor_other_coefficient]
  norm_num [Fin.prod_univ_succ, phaseAt3]
  ring_nf
  norm_num

end VortexGap.Examples
