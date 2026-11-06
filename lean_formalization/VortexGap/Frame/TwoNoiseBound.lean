import VortexGap.Frame.TwoNoiseFactorization
import VortexGap.Fermion.ExteriorNorm

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped BigOperators InnerProduct ComplexOrder

/-- The concrete two-environment relative estimate, with no N or dimension factor.
The only frame bound is the raw two-particle quadratic inequality Q<=beta I. -/
theorem twoLossNoise_relative {n : ℕ} {ι : Type*} [Fintype ι]
    (M : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (p : ι → PairSpace n) (β : ℝ) (hβ : 0 ≤ β)
    (hQ : ∀ q : PairSpace n,
      (inner ℂ q ((∑ i, (w i : ℂ) • pairRankOne (p i)) q)).re ≤ β * ‖q‖ ^ 2)
    (x : Space n) :
    ‖twoLossNoise M w p x‖ ^ 2 ≤ β * ‖1 - M ^ 2‖ ^ 2 * (inner ℂ x (filteredHamiltonian M w p x)).re := by
  have he := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (lossDefect_exteriorSquare_norm_le M hM hc)
  have hx : 0 ≤ (inner ℂ x (filteredHamiltonian M w p x)).re := by
    rw [← filtered_frameAnalysis_norm_sq M w hw p x]
    exact sq_nonneg _
  exact (twoLossNoise_exterior_bound M w hw p β hβ hQ x).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he hβ) hx)

/-- The same estimate in the project's real-quadratic-form convention. -/
theorem twoLossNoise_relative_form {n : ℕ} {ι : Type*} [Fintype ι]
    (M : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (p : ι → PairSpace n) (β : ℝ) (hβ : 0 ≤ β)
    (hQ : ∀ q : PairSpace n,
      (inner ℂ q ((∑ i, (w i : ℂ) • pairRankOne (p i)) q)).re ≤ β * ‖q‖ ^ 2)
    (x : Space n) :
    (inner ℂ x (((twoLossNoise M w p).adjoint.comp (twoLossNoise M w p)) x)).re ≤
      β * ‖1 - M ^ 2‖ ^ 2 * (inner ℂ x (filteredHamiltonian M w p x)).re := by
  rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right]
  simpa only [norm_sq_eq_re_inner (𝕜 := ℂ), RCLike.re_eq_complex_re] using
    twoLossNoise_relative M hM hc w hw p β hβ hQ x

end VortexGap.Fermion
