import VortexGap.Fermion.LossMoments
import VortexGap.Examples.TwoMode

noncomputable section
set_option autoImplicit false
namespace VortexGap.Examples
open VortexGap.Fermion OAI.LaughlinGap.Occupation
open scoped InnerProduct ComplexConjugate ComplexOrder

/-- Nonidentity positive contraction on a genuine two-mode space. -/
def lossFilter : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) := (3/5 : ℂ) • 1

theorem lossFilter_nonneg : 0 ≤ lossFilter := by
  unfold lossFilter
  exact smul_nonneg (by norm_num [Complex.le_def] : (0 : ℂ) ≤ 3/5)
    (show (0 : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)) ≤ 1 from zero_le_one)

theorem lossFilter_contraction : ‖lossFilter‖ ≤ 1 := by
  norm_num [lossFilter, norm_smul]

theorem lossFilter_defect : lossDefect lossFilter = (4/5 : ℂ) • 1 := by
  unfold lossDefect
  apply CFC.sqrt_unique
  · ext x i
    simp [lossFilter, pow_two, smul_eq_mul]
    ring
  · exact smul_nonneg (by norm_num [Complex.le_def] : (0 : ℂ) ≤ 4/5) zero_le_one

theorem loss_basis_create (i : Fin 2) : create (PiLp.single 2 i 1) = createMode i := by
  simp [create, PiLp.single_apply]

theorem loss_basis_vacuum (i : Fin 2) : createMode i (ket ∅) = ket {i} := by
  rw [createMode_ket i ∅ (by simp)]
  simp [sign]

theorem loss_pair_created : createMode (0 : Fin 2) (createMode 1 (ket ∅)) = ket {0,1} := by
  rw [loss_basis_vacuum, createMode_ket 0 {1} (by decide)]
  norm_num [sign, Finset.filter_singleton]

/-- All four amplitudes are nonzero. The mixed channels have opposite signs. -/
theorem loss_pair_creation_regression :
    fockSplit 2 2
      (pairCreate (exteriorSquare (finiteLossEmbedding lossFilter lossFilter_nonneg lossFilter_contraction).toLinearMap
        (wedgePair (PiLp.single 2 0 1) (PiLp.single 2 1 1)))
      ((fockSplit 2 2).symm (environmentVacuum 2 2 (ket ∅)))) =
    (9/25 : ℂ) • fockProduct (ket ∅) (ket {0,1}) +
      (12/25 : ℂ) • (fockProduct (ket {0}) (ket {1}) - fockProduct (ket {1}) (ket {0})) +
      (16/25 : ℂ) • fockProduct (ket {0,1}) (ket ∅) := by
  rw [loss_pairCreate_vacuum]
  simp only [oneLossCreation, twoLossCreation, exteriorSquare_wedge, ContinuousLinearMap.coe_coe]
  rw [lossFilter_defect]
  simp only [lossFilter, smul_apply, one_apply_eq_self,
    pairCreate_wedge, pairEmbed_wedge, Module.End.mul_apply, create_smul,
    loss_basis_create, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    map_smul, loss_pair_created, ← fockProduct_vacuum, smul_smul]
  simp only [loss_basis_vacuum]
  module

theorem loss_filtered_annihilation (x : Space 2) :
    pairAnnihilate (exteriorSquare lossFilter.toLinearMap
      (wedgePair (PiLp.single 2 0 1) (PiLp.single 2 1 1))) x =
      (9/25 : ℂ) • annihilateMode 1 (annihilateMode 0 x) := by
  rw [exteriorSquare_wedge, pairAnnihilate_wedge]
  norm_num [lossFilter, annihilate_smul, annihilate_basis, Module.End.mul_apply, map_smul, smul_smul, map_ofNat]

/-- Actual interaction output on a non-real two-particle input, with both noises present. -/
theorem loss_hamiltonian_complex_regression :
    fockSplit 2 2
      (lossHamiltonian lossFilter lossFilter_nonneg lossFilter_contraction
        (fun _ : Unit => 1) (fun _ => wedgePair (PiLp.single 2 0 1) (PiLp.single 2 1 1))
        (lossVacuum 2 (Complex.I • ket {0,1}))) =
    (81/625 * Complex.I : ℂ) • fockProduct (ket ∅) (ket {0,1}) +
      (108/625 * Complex.I : ℂ) • (fockProduct (ket {0}) (ket {1}) - fockProduct (ket {1}) (ket {0})) +
      (144/625 * Complex.I : ℂ) • fockProduct (ket {0,1}) (ket ∅) := by
  simp only [lossHamiltonian, frameHamiltonian, Fintype.sum_unique, Complex.ofReal_one, one_smul,
    pairLift_rankOne, pairAnnihilate_adjoint, Module.End.mul_apply, lossVacuum_apply]
  rw [loss_pairAnnihilate_vacuum, loss_filtered_annihilation]
  have ha := two_mode_pair
  change annihilateMode (1 : Fin 2) (annihilateMode 0 (ket {0,1})) = ket ∅ at ha
  simp only [map_smul, ha, loss_pair_creation_regression, smul_add, smul_smul]
  module

theorem lossFilter_ne_one : lossFilter ≠ 1 := by
  intro h
  have he := congrArg (fun T : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) =>
    T (PiLp.single 2 0 1) 0) h
  norm_num [lossFilter] at he

end VortexGap.Examples
