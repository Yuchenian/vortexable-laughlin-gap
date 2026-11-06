import VortexGap.Fermion.CountableOrbitalCAR
import Mathlib.Analysis.Calculus.Deriv.Mul
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped InnerProduct ComplexConjugate

/-- Product-rule contact amplitude in the actual completed CAR representation.
The derivative vector is arbitrary; no invertibility or nonvanishing of f is used. -/
theorem contact_field_cancel (v : CountableOrbital)
    (D : CountableSpace →L[ℂ] CountableSpace) (f df : ℂ) :
    (f • countableAnnihilate v) * (f • D + df • countableAnnihilate v) =
      f^2 • (countableAnnihilate v * D) := by
  simp only [mul_add, smul_mul_assoc, mul_smul_comm, smul_smul,
    countableAnnihilate_square, pow_two]
  ext x A
  simp

/-- The physical local contact energy acquires |f|^4, including at zeros of f. -/
theorem contact_field_energy (v : CountableOrbital)
    (D : CountableSpace →L[ℂ] CountableSpace) (f df : ℂ) (x : CountableSpace) :
    ‖((f • countableAnnihilate v) * (f • D + df • countableAnnihilate v)) x‖^2 =
      ‖f‖^4 * ‖(countableAnnihilate v * D) x‖^2 := by
  rw [contact_field_cancel]
  simp only [smul_apply, norm_smul, norm_pow]
  ring

/-- For a genuinely differentiable operator field along a real coordinate,
calculus supplies the product rule and CAR removes its derivative-of-f term.
Identifying this field with the planar LLL evaluation field is a separate task. -/
theorem differentiable_contact_cancel
    (χ : ℝ → (CountableSpace →L[ℂ] CountableSpace))
    (D : CountableSpace →L[ℂ] CountableSpace) (f : ℝ → ℂ)
    (df : ℂ) (r : ℝ) (v : CountableOrbital)
    (hχ : HasDerivAt χ D r) (hf : HasDerivAt f df r)
    (hv : χ r = countableAnnihilate v) :
    (f r • χ r) * deriv (fun t => f t • χ t) r =
      (f r)^2 • (χ r * D) := by
  rw [(hf.fun_smul hχ).deriv, hv]
  exact contact_field_cancel v D (f r) df

/-- Nonzero two-particle regression: complex f=2i and nonzero df=7.
This checks contact weighting, not a physical band example. -/
theorem contact_complex_regression :
    ‖(((2*Complex.I) • countableAnnihilate (orbitalKet 1)) *
      ((2*Complex.I) • countableAnnihilate (orbitalKet 0) +
        (7 : ℂ) • countableAnnihilate (orbitalKet 1))) (countableKet {0,1})‖^2 = 16 := by
  rw [contact_field_energy]
  have h0 : countableAnnihilate (orbitalKet 0) (countableKet {0,1}) = countableKet {1} := by
    rw [countableAnnihilate_ket, countableAnnihilateMode_ket 0 _ (by simp)]
    simp [countableSign]
  have h1 : countableAnnihilate (orbitalKet 1) (countableKet {1}) = countableKet ∅ := by
    rw [countableAnnihilate_ket, countableAnnihilateMode_ket 1 _ (by simp)]
    simp [countableSign, Finset.filter_singleton]
  change ‖2*Complex.I‖^4 * ‖countableAnnihilate (orbitalKet 1)
    (countableAnnihilate (orbitalKet 0) (countableKet {0,1}))‖^2 = 16
  rw [h0, h1, countableKet_norm]
  norm_num [norm_mul]

end VortexGap.Fermion
