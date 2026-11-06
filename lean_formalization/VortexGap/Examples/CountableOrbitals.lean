import VortexGap.Fermion.CountableOrbitalActions

noncomputable section
set_option autoImplicit false
namespace VortexGap.Examples
open Fermion
open scoped InnerProduct ComplexConjugate ENNReal

theorem geometricCoefficient_norm_sq (j : ℕ) :
    ‖(Complex.I / 2 : ℂ) ^ j‖ ^ 2 = (1 / 4 : ℝ) ^ j := by
  have h : ‖(Complex.I / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num [norm_div]
  rw [norm_pow, h, pow_two, ← mul_pow]
  norm_num

/-- A genuinely infinite-support complex orbital; no finite orbital cutoff enters the definition. -/
def geometricOrbital : CountableOrbital :=
  ⟨fun j => (Complex.I / 2 : ℂ) ^ j, by
    apply memℓp_gen
    have h : Summable (fun j : ℕ => (1 / 4 : ℝ) ^ j) :=
      summable_geometric_of_norm_lt_one (by norm_num)
    simpa only [show (2 : ℝ≥0∞).toReal = (2 : ℝ) by norm_num,
      Real.rpow_two, geometricCoefficient_norm_sq] using h⟩

def geometricOneParticle : CountableSpace := countableCreate geometricOrbital (countableKet ∅)

theorem geometricOrbital_coefficient (j : ℕ) : geometricOrbital j = (Complex.I / 2 : ℂ) ^ j := rfl

theorem geometricOrbital_coefficient_ne_zero (j : ℕ) : geometricOrbital j ≠ 0 := by
  rw [geometricOrbital_coefficient]
  exact pow_ne_zero j (by norm_num)

theorem geometricOrbital_ne_zero : geometricOrbital ≠ 0 := by
  intro h
  have hz := geometricOrbital_coefficient_ne_zero 0
  exact hz (by rw [h]; rfl)

theorem geometricOrbital_norm_sq : ‖geometricOrbital‖ ^ 2 = (4 / 3 : ℝ) := by
  calc
    _ = ∑' j, ‖geometricOrbital j‖ ^ 2 := by
      simpa using lp.norm_rpow_eq_tsum (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal) geometricOrbital
    _ = ∑' j : ℕ, (1 / 4 : ℝ) ^ j := by
      simp only [geometricOrbital_coefficient, geometricCoefficient_norm_sq]
    _ = _ := by
      rw [tsum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 4 : ℝ)‖ < 1)]
      norm_num

theorem geometricOneParticle_sector : geometricOneParticle ∈ countableSector 1 :=
  countableCreate_sector geometricOrbital (by simpa using countableKet_sector ∅)

theorem geometricOneParticle_norm_sq : ‖geometricOneParticle‖ ^ 2 = (4 / 3 : ℝ) := by
  rw [geometricOneParticle, countableCreate_vacuum_norm, geometricOrbital_norm_sq]

theorem geometricOneParticle_ne_zero : geometricOneParticle ≠ 0 := by
  intro h
  have hn := geometricOneParticle_norm_sq
  rw [h] at hn
  norm_num at hn

/-- The imaginary phase is conjugated by annihilation, on an actual nonzero l2 state. -/
theorem geometric_imaginary_annihilation :
    countableAnnihilate (Complex.I • geometricOrbital) geometricOneParticle =
      ((-4 / 3 : ℂ) * Complex.I) • countableKet ∅ := by
  have hi : inner ℂ geometricOrbital geometricOrbital = (4 / 3 : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, geometricOrbital_norm_sq]
    norm_num
  rw [geometricOneParticle, countableAnnihilate_create_vacuum, inner_smul_left, hi]
  congr 1
  norm_num <;> ring

theorem geometric_repeated_creation_zero :
    countableCreate geometricOrbital geometricOneParticle = 0 := by
  exact congrArg (fun T : CountableSpace →L[ℂ] CountableSpace => T (countableKet ∅))
    (countableCreate_square geometricOrbital)

end VortexGap.Examples
