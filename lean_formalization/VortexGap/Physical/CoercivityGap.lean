import VortexGap.Physical.PairCoercivity
import VortexGap.Physical.KernelGap
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped InnerProduct ComplexOrder

theorem operator_le_energy {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A B : H →L[ℂ] H) (h : A ≤ B) (x : H) :
    (inner ℂ x (A x)).re ≤ (inner ℂ x (B x)).re := by
  have hh := (ContinuousLinearMap.le_def.mp h).re_inner_nonneg_right x
  change 0 ≤ (inner ℂ x ((B-A) x)).re at hh
  simpa only [sub_apply, inner_sub_right, Complex.sub_re, sub_nonneg] using hh

theorem operator_scaled_le_energy {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A B : H →L[ℂ] H) (c : ℝ) (h : (c : ℂ) • A ≤ B) (x : H) :
    c*(inner ℂ x (A x)).re ≤ (inner ℂ x (B x)).re := by
  have hh := operator_le_energy _ _ h x
  simp only [smul_apply, inner_smul_right, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] at hh
  exact hh

theorem operator_le_scaled_energy {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A B : H →L[ℂ] H) (c : ℝ) (h : A ≤ (c : ℂ) • B) (x : H) :
    (inner ℂ x (A x)).re ≤ c*(inner ℂ x (B x)).re := by
  have hh := operator_le_energy _ _ h x
  simp only [smul_apply, inner_smul_right, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] at hh
  exact hh

/-- Lower-level comparison assembly: the gap of the actual normalized filtered
reference is explicit here. The continuous-transfer entrance supplies it later. -/
theorem filtered_coercivity_kernel_gap (N : ℕ)
    (R : CountableOrbital →L[ℂ] CountableOrbital) (hR : 0 ≤ R)
    (Q W : CountablePairSpace →L[ℂ] CountablePairSpace) (hQ : 0 ≤ Q)
    (κ K g γ : ℝ) (hκ : 0 < κ) (hg : 0 < g)
    (hlo : (κ : ℂ) • Q ≤ W) (hhi : W ≤ (K : ℂ) • Q) :
    let M := (Real.sqrt g : ℂ) • R
    let hM : 0 ≤ M := smul_nonneg
      (show 0 ≤ (Real.sqrt g : ℂ) by exact_mod_cast Real.sqrt_nonneg g) hR
    let B := filteredPairHamiltonian N M hM Q
    let A := filteredPairHamiltonian N R hR W
    (B*B-(γ : ℂ) • B).IsPositive →
      LinearMap.ker A.toLinearMap = LinearMap.ker B.toLinearMap ∧
      ∀ x ∈ (LinearMap.ker A.toLinearMap)ᗮ,
        (κ/g^2*γ) * ‖x‖^2 ≤ (inner ℂ x (A x)).re := by
  dsimp only
  intro hgap
  let M := (Real.sqrt g : ℂ) • R
  have hM : 0 ≤ M := smul_nonneg
    (show 0 ≤ (Real.sqrt g : ℂ) by exact_mod_cast Real.sqrt_nonneg g) hR
  let A := filteredPairHamiltonian N R hR W
  let B := filteredPairHamiltonian N M hM Q
  have hW : 0 ≤ W := (smul_nonneg (show 0 ≤ (κ : ℂ) by exact_mod_cast hκ.le) hQ).trans hlo
  have hA : 0 ≤ A := ContinuousLinearMap.nonneg_iff_isPositive.mpr
    (filteredPairHamiltonian_positive N R hR W (ContinuousLinearMap.nonneg_iff_isPositive.mp hW))
  have hB : 0 ≤ B := ContinuousLinearMap.nonneg_iff_isPositive.mpr
    (filteredPairHamiltonian_positive N M hM Q (ContinuousLinearMap.nonneg_iff_isPositive.mp hQ))
  have hb := filteredPairHamiltonian_normalized_coercivity N R hR Q W κ K g hg hlo hhi
  have hl (x : countableSector N) : (κ/g^2)*(inner ℂ x (B x)).re ≤ (inner ℂ x (A x)).re :=
    operator_scaled_le_energy B A _ hb.1 x
  have hu (x : countableSector N) : (inner ℂ x (A x)).re ≤ (K/g^2)*(inner ℂ x (B x)).re :=
    operator_le_scaled_energy A B _ hb.2 x
  have hp : 0 < κ/g^2 := div_pos hκ (sq_pos_of_pos hg)
  exact ⟨positive_form_comparison_kernel A B hA hB _ _ hp hl hu,
    positive_form_comparison_of_quadratic_gap A B hA hB _ _ γ hp hl hu hgap⟩

end VortexGap.Fermion
