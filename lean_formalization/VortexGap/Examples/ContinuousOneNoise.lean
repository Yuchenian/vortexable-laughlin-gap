import VortexGap.Frame.ContinuousOneNoiseBound
import VortexGap.Frame.ModeFrames
import VortexGap.Examples.ContinuousPhase

noncomputable section
set_option autoImplicit false
namespace VortexGap.Examples
open VortexGap.Fermion VortexGap.Frame MeasureTheory OAI.LaughlinGap.Occupation
open scoped InnerProduct ComplexConjugate ENNReal

/-- Constant normalized orbitals, with actual Lebesgue labels on [0,1]. -/
def intervalOrbital (i : Fin 2) (_t : ℝ) : EuclideanSpace ℂ (Fin 2) := PiLp.single 2 i 1

theorem intervalOrbital_measurable (i : Fin 2) : AEStronglyMeasurable (intervalOrbital i) phaseMeasure :=
  aestronglyMeasurable_const

theorem intervalOrbital_norm (i : Fin 2) (t : ℝ) : ‖intervalOrbital i t‖ ≤ 1 := by
  simp [intervalOrbital]

/-- Both the existence and bound of the raw overlap row are verified. -/
theorem intervalOneNoise_schur :
    (∀ᵐ a : ℝ ∂phaseMeasure, Integrable (fun _b : ℝ =>
      traceNormTwo (twoFrameOverlap
        (LinearIsometry.id : TwoFrame 2)
        (LinearIsometry.id : TwoFrame 2)) * (1:ℝ)) phaseMeasure) ∧
    (∀ᵐ a : ℝ ∂phaseMeasure, (∫ _b : ℝ, traceNormTwo (twoFrameOverlap
        (LinearIsometry.id : TwoFrame 2)
        (LinearIsometry.id : TwoFrame 2)) * (1:ℝ) ∂phaseMeasure) ≤ 2 * (1:ℝ)) := by
  simp only [twoFrameOverlap_self, traceNormTwo_id, mul_one]
  constructor
  · exact Filter.Eventually.of_forall fun _ => integrable_const 2
  · exact Filter.Eventually.of_forall fun _ => by
      rw [integral_const, phaseMeasure_mass, one_smul]

private theorem intervalOneNoise_integrand (t : ℝ) :
    oneLossCreation lossFilter (intervalOrbital 0 t) (intervalOrbital 1 t)
      (pairAnnihilate (exteriorSquare lossFilter.toLinearMap
        (wedgePair (intervalOrbital 0 t) (intervalOrbital 1 t))) (Complex.I • ket {0,1})) =
      (108/625 * Complex.I : ℂ) •
        (fockProduct (ket {0}) (ket {1}) - fockProduct (ket {1}) (ket {0})) := by
  change oneLossCreation lossFilter (PiLp.single 2 0 1) (PiLp.single 2 1 1)
    (pairAnnihilate (exteriorSquare lossFilter.toLinearMap weightedUnitPair) (Complex.I • ket {0,1})) = _
  rw [weighted_filtered_pair_input]
  simp only [oneLossCreation]
  rw [lossFilter_defect]
  simp only [lossFilter, ContinuousLinearMap.coe_coe,
    smul_apply, one_apply_eq_self, create_smul, loss_basis_create,
    LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, map_smul, loss_basis_vacuum]
  module

/-- Nonzero complex input; the two one-environment channels have opposite CAR signs. -/
theorem intervalOneNoise_output :
    continuousOneLossNoise lossFilter phaseMeasure (intervalOrbital 0) (intervalOrbital 1)
      (Complex.I • ket {0,1}) = (108/625 * Complex.I : ℂ) •
        (fockProduct (ket {0}) (ket {1}) - fockProduct (ket {1}) (ket {0})) := by
  rw [continuousOneLossNoise_apply lossFilter phaseMeasure _ _
    (intervalOrbital_measurable 0) (intervalOrbital_measurable 1)
    (intervalOrbital_norm 0) (intervalOrbital_norm 1)]
  simp_rw [intervalOneNoise_integrand]
  rw [integral_const, phaseMeasure_mass, one_smul]

theorem intervalOneNoise_norm_sq :
    ‖continuousOneLossNoise lossFilter phaseMeasure (intervalOrbital 0) (intervalOrbital 1)
      (Complex.I • ket {0,1})‖^2 = (23328/390625:ℝ) := by
  have hf : ‖fockProduct (ket {0} : Space 2) (ket {1} : Space 2) -
      fockProduct (ket {1} : Space 2) (ket {0} : Space 2)‖^2 = (2:ℝ) := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
    simp only [inner_sub_left, inner_sub_right, fockProduct_inner]
    norm_num [ket, EuclideanSpace.inner_single_left, PiLp.single_apply]
  rw [intervalOneNoise_output, norm_smul, mul_pow]
  norm_num [norm_mul, hf]

theorem intervalOneNoise_energy :
    (inner ℂ (Complex.I • ket {0,1})
      (continuousFrameHamiltonian phaseMeasure
        (fun _ : ℝ => exteriorSquare lossFilter.toLinearMap weightedUnitPair)
        (Complex.I • ket {0,1}))).re = (81/625:ℝ) := by
  have hp : MemLp (fun _ : ℝ => exteriorSquare lossFilter.toLinearMap weightedUnitPair) 2 phaseMeasure :=
    MemLp.of_bound aestronglyMeasurable_const _ (Filter.Eventually.of_forall fun _ => le_refl _)
  rw [continuousFrameHamiltonian_energy phaseMeasure _ hp]
  simp_rw [weighted_filtered_pair_input, norm_smul, norm_mul, Complex.norm_I, ket_norm]
  norm_num [integral_const, phaseMeasure_mass]

/-- Instantiate the general continuous X1 bound, with all hypotheses discharged. -/
theorem intervalOneNoise_relative_instance :
    ‖continuousOneLossNoise lossFilter phaseMeasure (intervalOrbital 0) (intervalOrbital 1)
      (Complex.I • ket {0,1})‖^2 ≤ (2592/15625:ℝ) := by
  have h := continuousOneLossNoise_relative lossFilter phaseMeasure lossFilter_nonneg lossFilter_contraction
    (fun _ : ℝ => (LinearIsometry.id : TwoFrame 2))
    (intervalOrbital_measurable 0) (intervalOrbital_measurable 1)
    (fun _ => 1) (fun _ => by norm_num) aestronglyMeasurable_const 2
    intervalOneNoise_schur.1 intervalOneNoise_schur.2 (Complex.I • ket {0,1})
  change _ ≤ 2 * ‖1 - lossFilter^2‖ * (inner ℂ (Complex.I • ket {0,1})
    (continuousFrameHamiltonian phaseMeasure
      (fun _ : ℝ => exteriorSquare lossFilter.toLinearMap weightedUnitPair)
      (Complex.I • ket {0,1}))).re at h
  rw [weighted_loss_delta, intervalOneNoise_energy] at h
  norm_num at h ⊢
  exact h

theorem intervalOneNoise_nonzero :
    continuousOneLossNoise lossFilter phaseMeasure (intervalOrbital 0) (intervalOrbital 1)
      (Complex.I • ket {0,1}) ≠ 0 := by
  intro hz
  have h := intervalOneNoise_norm_sq
  rw [hz] at h
  norm_num at h

end VortexGap.Examples

