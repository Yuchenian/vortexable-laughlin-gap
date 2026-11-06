import VortexGap.Fermion.LossMoments

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped BigOperators InnerProduct ComplexConjugate

/-- Synthesis with the square root of the actual nonnegative measure weight. -/
def pairSynthesis {n : ℕ} {ι : Type*} [Fintype ι] (w : ι → ℝ) (p : ι → PairSpace n) :
    EuclideanSpace ℂ ι →ₗ[ℂ] PairSpace n where
  toFun f := ∑ i, ((Real.sqrt (w i) : ℂ) * f i) • p i
  map_add' f g := by simp [mul_add, add_smul, Finset.sum_add_distrib]
  map_smul' z f := by simp [Finset.smul_sum, smul_smul, mul_left_comm]

theorem pairSynthesis_apply {n : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (p : ι → PairSpace n) (f : EuclideanSpace ℂ ι) :
    pairSynthesis w p f = ∑ i, ((Real.sqrt (w i) : ℂ) * f i) • p i := rfl

theorem pairSynthesis_basis {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℝ) (p : ι → PairSpace n) (i : ι) :
    pairSynthesis w p (PiLp.single 2 i 1) = (Real.sqrt (w i) : ℂ) • p i := by
  simp [pairSynthesis_apply, PiLp.single_apply]

theorem pairSynthesis_adjoint_apply {n : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (p : ι → PairSpace n) (q : PairSpace n) (i : ι) :
    (pairSynthesis w p).adjoint q i = (Real.sqrt (w i) : ℂ) * inner ℂ (p i) q := by
  classical
  have h := LinearMap.adjoint_inner_right (pairSynthesis w p) (PiLp.single 2 i 1) q
  simpa only [EuclideanSpace.inner_single_left, map_one, one_mul, pairSynthesis_basis,
    inner_smul_left, Complex.conj_ofReal] using h

theorem weightRoot_mul {a : ℝ} (ha : 0 ≤ a) :
    (Real.sqrt a : ℂ) * (Real.sqrt a : ℂ) = (a : ℂ) := by
  exact_mod_cast Real.mul_self_sqrt ha

/-- The weighted pair operator is obtained from the constructed synthesis map. -/
theorem pairSynthesis_gram {n : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (p : ι → PairSpace n) :
    (pairSynthesis w p).comp (pairSynthesis w p).adjoint =
      ∑ i, (w i : ℂ) • pairRankOne (p i) := by
  apply LinearMap.ext
  intro q
  simp only [LinearMap.comp_apply, pairSynthesis_apply, pairSynthesis_adjoint_apply,
    LinearMap.sum_apply, LinearMap.smul_apply]
  apply Finset.sum_congr rfl
  intro i _
  change ((Real.sqrt (w i) : ℂ) * ((Real.sqrt (w i) : ℂ) * inner ℂ (p i) q)) • p i =
    (w i : ℂ) • ((inner ℂ (p i) q) • p i)
  rw [← mul_assoc, weightRoot_mul (hw i), smul_smul]

theorem frameHamiltonian_energy {n : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (p : ι → PairSpace n) (x : Space n) :
    (inner ℂ x (frameHamiltonian w p x)).re = ∑ i, w i * ‖pairAnnihilate (p i) x‖ ^ 2 := by
  unfold frameHamiltonian
  rw [pairLift_frame]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, inner_sum, inner_smul_right, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Module.End.mul_apply, LinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  simp [← Complex.ofReal_pow]

abbrev FrameStackSpace (ι : Type*) [Fintype ι] (n : ℕ) :=
  EuclideanSpace ℂ (ι × Finset (Fin n))

/-- Actual finite frame analysis into the l2 sum of full Fock outputs. -/
def frameAnalysis {n : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (p : ι → PairSpace n) : Space n →ₗ[ℂ] FrameStackSpace ι n where
  toFun x := WithLp.toLp 2 (fun iA => (Real.sqrt (w iA.1) : ℂ) * pairAnnihilate (p iA.1) x iA.2)
  map_add' x y := by ext iA; simp [mul_add]
  map_smul' z x := by ext iA; simp [mul_left_comm]

theorem frameAnalysis_apply {n : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (p : ι → PairSpace n) (x : Space n) (i : ι) (A : Finset (Fin n)) :
    frameAnalysis w p x (i,A) = (Real.sqrt (w i) : ℂ) * pairAnnihilate (p i) x A := rfl

theorem frameAnalysis_norm_sq {n : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (p : ι → PairSpace n) (x : Space n) :
    ‖frameAnalysis w p x‖ ^ 2 = (inner ℂ x (frameHamiltonian w p x)).re := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, frameHamiltonian_energy]
  apply Finset.sum_congr rfl
  intro i _
  simp only [frameAnalysis_apply, norm_mul, mul_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hw i),
    ← Finset.mul_sum, EuclideanSpace.norm_sq_eq]

theorem filtered_frameAnalysis_norm_sq {n : ℕ} {ι : Type*} [Fintype ι]
    (M : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (p : ι → PairSpace n) (x : Space n) :
    ‖frameAnalysis w (fun i => exteriorSquare M.toLinearMap (p i)) x‖ ^ 2 =
      (inner ℂ x (filteredHamiltonian M w p x)).re :=
  frameAnalysis_norm_sq w hw _ x

/-- The raw two-particle quadratic upper bound controls synthesis, without a label-count factor. -/
theorem pairSynthesis_norm_sq_le {n : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (p : ι → PairSpace n) (β : ℝ) (hβ : 0 ≤ β)
    (hQ : ∀ q : PairSpace n,
      (inner ℂ q ((∑ i, (w i : ℂ) • pairRankOne (p i)) q)).re ≤ β * ‖q‖ ^ 2)
    (f : EuclideanSpace ℂ ι) : ‖pairSynthesis w p f‖ ^ 2 ≤ β * ‖f‖ ^ 2 := by
  let S := pairSynthesis w p
  have ha : ‖S.adjoint (S f)‖ ^ 2 ≤ β * ‖S f‖ ^ 2 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), LinearMap.adjoint_inner_left]
    change (inner ℂ (S f) ((S.comp S.adjoint) (S f))).re ≤ _
    rw [pairSynthesis_gram w hw p]
    exact hQ _
  have hc : ‖S f‖ ^ 2 ≤ ‖S.adjoint (S f)‖ * ‖f‖ := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), ← LinearMap.adjoint_inner_left S f (S f)]
    exact re_inner_le_norm (𝕜 := ℂ) _ _
  have hc2 := (sq_le_sq₀ (sq_nonneg ‖S f‖)
    (mul_nonneg (norm_nonneg (S.adjoint (S f))) (norm_nonneg f))).mpr hc
  rw [mul_pow] at hc2
  have hh := mul_le_mul_of_nonneg_right ha (sq_nonneg ‖f‖)
  change ‖S f‖ ^ 2 ≤ β * ‖f‖ ^ 2
  by_cases hz : ‖S f‖ = 0
  · rw [hz, zero_pow (by decide)]
    exact mul_nonneg hβ (sq_nonneg _)
  · have hp : 0 < ‖S f‖ ^ 2 := sq_pos_of_ne_zero hz
    nlinarith only [hc2, hh, hp]

end VortexGap.Fermion
