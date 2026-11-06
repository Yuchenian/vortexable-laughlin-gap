import OAI.Analysis.Laughlin.Tensor.PolynomialRealization
import VortexGap.Geometry.SphereSpinColumns
import Mathlib.Algebra.Polynomial.Coeff
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open OAI.Laughlin.Rotation Polynomial
open scoped Polynomial Matrix

private theorem spin_coeff (Q : ℕ) (g : SourceSU2) (i j : Fin (Q+1)) :
    sourceSpinRepresentation Q g i j * (Real.sqrt (Q.choose i.val : ℝ) : ℂ) =
    (Real.sqrt (Q.choose j.val : ℝ) : ℂ) *
      (((C (g.val 0 1)+C (g.val 1 1)*X)^j.val *
        (C (g.val 0 0)+C (g.val 1 0)*X)^(Q-j.val)).coeff i.val) := by
  have h := congrArg (fun P : ℂ[X] => P.coeff i.val)
    (sourceSpinRepresentation_polynomial C Q g 1 X j)
  simp only [one_pow, mul_one, ← mul_assoc, ← map_mul, finsetSum_coeff,
    coeff_C_mul, coeff_X_pow, mul_ite, mul_zero] at h
  simpa [← Fin.ext_iff, mul_assoc, coeff_C_mul, ← C_mul] using h

private theorem linear_pow_coeff_one (a b : ℂ) (n : ℕ) :
    ((C a + C b * X)^n).coeff 1 = n*b*a^(n-1) := by
  induction n with
  | zero => simp [coeff_one]
  | succ n ih =>
    rw [pow_succ, mul_coeff_one, ih]
    simp [coeff_mul_X, coeff_zero_eq_eval_zero]
    cases n <;> push_cast <;> simp [pow_succ] <;> ring

theorem sphereSpinBlock_first_row (Q : ℕ) (g : SourceSU2) (j : Fin (Q+1)) :
    sourceSpinRepresentation Q g 0 j =
      (Real.sqrt (Q.choose j.val : ℝ) : ℂ) * (g.val 0 1)^j.val * (g.val 0 0)^(Q-j.val) := by
  simpa [coeff_zero_eq_eval_zero, mul_assoc] using spin_coeff Q g 0 j

theorem sphereSpinBlock_second_row (n : ℕ) (g : SourceSU2) (j : Fin (n+1+1)) :
    sourceSpinRepresentation (n+1) g 1 j * (Real.sqrt ((n+1:ℕ):ℝ) : ℂ) =
      (Real.sqrt ((n+1).choose j.val : ℝ) : ℂ) *
      ((g.val 0 1)^j.val * ((n+1-j.val:ℕ) * (g.val 1 0) * (g.val 0 0)^(n+1-j.val-1)) +
       (j.val * (g.val 1 1) * (g.val 0 1)^(j.val-1)) * (g.val 0 0)^(n+1-j.val)) := by
  have h := spin_coeff (n+1) g 1 j
  rw [Fin.val_one, Nat.choose_one_right, mul_coeff_one, linear_pow_coeff_one, linear_pow_coeff_one] at h
  simpa [coeff_zero_eq_eval_zero] using h

/-- At flux n+2 the highest-weight block has a common power without negative exponents. -/
theorem sphereSpinBlock_entries (n : ℕ) (g : SourceSU2) :
    let ρ := sourceSpinRepresentation (n+2) g
    let a := g.val 0 0
    let b := g.val 0 1
    let c := g.val 1 0
    let d := g.val 1 1
    let r : ℂ := Real.sqrt ((n+2:ℕ):ℝ)
    ρ 0 0 = a^(n+2) ∧ ρ 0 1 = r*b*a^(n+1) ∧
    ρ 1 0 = r*c*a^(n+1) ∧ ρ 1 1 = a^n*(a*d+(n+1)*b*c) := by
  dsimp only
  let r : ℂ := Real.sqrt ((n+2:ℕ):ℝ)
  have hr : r ≠ 0 := by apply Complex.ofReal_ne_zero.mpr; apply Real.sqrt_ne_zero'.mpr; positivity
  have hr2 : r*r = ((n+2:ℕ):ℂ) := by
    dsimp [r]
    exact_mod_cast Real.mul_self_sqrt (show 0 ≤ ((n+2:ℕ):ℝ) by positivity)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using sphereSpinBlock_first_row (n+2) g 0
  · simpa using sphereSpinBlock_first_row (n+2) g 1
  · apply mul_right_cancel₀ hr
    have h := sphereSpinBlock_second_row (n+1) g 0
    simp only [Fin.val_zero, Nat.choose_zero_right, Nat.cast_one, Real.sqrt_one,
      Complex.ofReal_one, pow_zero, one_mul, Nat.sub_zero, Nat.add_sub_cancel,
      Nat.cast_zero, zero_mul, add_zero] at h
    rw [h]
    change ((n+2:ℕ):ℂ) * _ * _ = r * _ * _ * r
    rw [← hr2]; ring
  · apply mul_right_cancel₀ hr
    have h := sphereSpinBlock_second_row (n+1) g 1
    simp only [Fin.val_one, Nat.choose_one_right, pow_one, Nat.add_sub_cancel,
      Nat.cast_one, one_mul, Nat.sub_self, pow_zero, mul_one] at h
    rw [h]
    dsimp [r]
    push_cast
    rw [pow_succ]
    ring

/-- The oriented pair overlap at flux n+2 is a single spinor monomial. -/
theorem sphereSpinColumns_pair_det (n : ℕ) (g h : SourceSU2) :
    ((sphereSpinColumns (n+1) g)ᴴ * sphereSpinColumns (n+1) h).det =
      ((g⁻¹*h).val 0 0)^(2*(n+1)) := by
  let k := g⁻¹*h
  obtain ⟨h00,h01,h10,h11⟩ := sphereSpinBlock_entries n k
  have hd : k.val.det = 1 := k.property.2
  rw [Matrix.det_fin_two] at hd
  have hs : (Real.sqrt ((n+2:ℕ):ℝ) : ℂ)^2 = ((n+2:ℕ):ℂ) := by
    exact_mod_cast Real.sq_sqrt (show 0 ≤ ((n+2:ℕ):ℝ) by positivity)
  rw [Matrix.det_fin_two]
  simp only [sphereSpinColumns_overlap]
  change sourceSpinRepresentation (n+2) k 0 0 * sourceSpinRepresentation (n+2) k 1 1 -
    sourceSpinRepresentation (n+2) k 0 1 * sourceSpinRepresentation (n+2) k 1 0 = _
  rw [h00,h01,h10,h11]
  change _ = (k.val 0 0)^(2*(n+1))
  rw [show 2*(n+1)=(n+1)*2 by omega, pow_mul]
  simp only [pow_succ, Nat.cast_add, Nat.cast_ofNat] at hs ⊢
  linear_combination (k.val 0 0 ^ n * k.val 0 0)^2 * hd -
    (k.val 0 0 ^ n * k.val 0 0)^2 * k.val 0 1 * k.val 1 0 * hs

theorem sphereSpinColumns_flux_one (g h : SourceSU2) :
    (sphereSpinColumns 0 g)ᴴ * sphereSpinColumns 0 h = (g⁻¹*h).val := by
  ext i j
  rw [sphereSpinColumns_overlap]
  fin_cases i <;> fin_cases j
  · simpa using sphereSpinBlock_first_row 1 (g⁻¹*h) 0
  · simpa using sphereSpinBlock_first_row 1 (g⁻¹*h) 1
  · simpa using sphereSpinBlock_second_row 0 (g⁻¹*h) 0
  · simpa using sphereSpinBlock_second_row 0 (g⁻¹*h) 1

end VortexGap.Fermion
