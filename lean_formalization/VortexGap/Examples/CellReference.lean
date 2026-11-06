import VortexGap.Transfer.FiniteFrame

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped BigOperators InnerProduct ComplexConjugate
open OAI.LaughlinGap.Occupation

/-- Each canonical pair term counts whether both orbitals are occupied. -/
theorem pairMode_occupation {n : ℕ} (a : PairIndex n) (x : Space n) (A : Finset (Fin n)) :
    ((pairMode a).adjoint * pairMode a) x A =
      if a.val.1 ∈ A ∧ a.val.2 ∈ A then x A else 0 := by
  rw [pairMode_adjoint]
  change createMode a.val.1 ((createMode a.val.2 * annihilateMode a.val.2)
    (annihilateMode a.val.1 x)) A = _
  have hn : a.val.2 ≠ a.val.1 := ne_of_gt a.property
  by_cases hi : a.val.1 ∈ A <;> by_cases hj : a.val.2 ∈ A <;>
    simp [createMode, creation, transition_apply,
      annihilateMode, annihilation, hi, hj, hn, ← mul_assoc]

theorem pairAnnihilate_pairBasis {n : ℕ} (a : PairIndex n) :
    pairAnnihilate (pairBasis a) = pairMode a := by
  simp [pairAnnihilate, pairBasis, PiLp.single_apply]

/-- Number of fully occupied selected pairs, including repetitions if present. -/
def modePairCount {n : ℕ} {ι : Type*} [Fintype ι]
    (a : ι → PairIndex n) (A : Finset (Fin n)) : ℕ :=
  ∑ i, if (a i).val.1 ∈ A ∧ (a i).val.2 ∈ A then 1 else 0

theorem modePairHamiltonian_apply {n : ℕ} {ι : Type*} [Fintype ι]
    (a : ι → PairIndex n) (x : Space n) (A : Finset (Fin n)) :
    frameHamiltonian (fun _ => 1) (fun i => pairBasis (a i)) x A =
      (modePairCount a A : ℂ) * x A := by
  rw [frameHamiltonian, pairLift_frame]
  simp only [Complex.ofReal_one, one_smul, pairAnnihilate_pairBasis, LinearMap.sum_apply,
    WithLp.ofLp_sum, Finset.sum_apply, pairMode_occupation]
  simp only [modePairCount, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    Finset.sum_mul, ite_mul, one_mul, zero_mul]

private theorem scalar_count_inner (m : ℕ) (z : ℂ) :
    (inner ℂ z ((m : ℂ) * z)).re = (m : ℝ) * ‖z‖^2 := by
  change (((m : ℂ) * z) * conj z).re = _
  rw [mul_assoc, Complex.mul_conj']
  simp [← Complex.ofReal_pow]

private theorem scalar_count_inner_square (m : ℕ) (z : ℂ) :
    (inner ℂ z ((m : ℂ) * ((m : ℂ) * z))).re = (m : ℝ)^2 * ‖z‖^2 := by
  rw [← mul_assoc, ← Nat.cast_mul, scalar_count_inner]
  simp [pow_two]

theorem modePairHamiltonian_energy {n : ℕ} {ι : Type*} [Fintype ι]
    (a : ι → PairIndex n) (x : Space n) :
    (inner ℂ x (frameHamiltonian (fun _ => 1) (fun i => pairBasis (a i)) x)).re =
      ∑ A, (modePairCount a A : ℝ) * ‖x A‖^2 := by
  simp only [PiLp.inner_apply, Complex.re_sum, modePairHamiltonian_apply, scalar_count_inner]

theorem modePairHamiltonian_energy_square {n : ℕ} {ι : Type*} [Fintype ι]
    (a : ι → PairIndex n) (x : Space n) :
    (inner ℂ x ((frameHamiltonian (fun _ => 1) (fun i => pairBasis (a i)) *
      frameHamiltonian (fun _ => 1) (fun i => pairBasis (a i))) x)).re =
      ∑ A, (modePairCount a A : ℝ)^2 * ‖x A‖^2 := by
  simp only [Module.End.mul_apply, PiLp.inner_apply, Complex.re_sum,
    modePairHamiltonian_apply, scalar_count_inner_square]

/-- An independently closed full finite-Fock gap; no reference gap premise is used. -/
theorem modePairHamiltonian_gap {n : ℕ} {ι : Type*} [Fintype ι]
    (a : ι → PairIndex n) (x : Space n) :
    (inner ℂ x (frameHamiltonian (fun _ => 1) (fun i => pairBasis (a i)) x)).re ≤
    (inner ℂ x ((frameHamiltonian (fun _ => 1) (fun i => pairBasis (a i)) *
      frameHamiltonian (fun _ => 1) (fun i => pairBasis (a i))) x)).re := by
  rw [modePairHamiltonian_energy, modePairHamiltonian_energy_square]
  apply Finset.sum_le_sum
  intro A _
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  have hnat : modePairCount a A ≤ (modePairCount a A)^2 := by
    simpa only [pow_two] using Nat.le_mul_self (modePairCount a A)
  exact_mod_cast hnat

end VortexGap.Fermion
