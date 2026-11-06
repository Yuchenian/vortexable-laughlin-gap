import VortexGap.Fermion.CountablePairEnvironment
import VortexGap.Frame.WeightedFrame
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped BigOperators InnerProduct ComplexConjugate

/-- Actual finite-label synthesis into the completed pair Hilbert space. -/
def countableScalarPairSynthesis {ι : Type*} [Fintype ι] (w : ι → ℝ)
    (p : ι → CountablePairSpace) : EuclideanSpace ℂ ι →L[ℂ] CountablePairSpace :=
  (show EuclideanSpace ℂ ι →ₗ[ℂ] CountablePairSpace from
    { toFun := fun f => ∑ i, ((Real.sqrt (w i) : ℂ) * f i) • p i
      map_add' := by intro f g; simp [mul_add, add_smul, Finset.sum_add_distrib]
      map_smul' := by intro c f; simp [Finset.smul_sum, smul_smul, mul_left_comm] }).toContinuousLinearMap

theorem countableScalarPairSynthesis_apply {ι : Type*} [Fintype ι] (w : ι → ℝ)
    (p : ι → CountablePairSpace) (f : EuclideanSpace ℂ ι) :
    countableScalarPairSynthesis w p f = ∑ i, ((Real.sqrt (w i) : ℂ) * f i) • p i := rfl

theorem countableScalarPairSynthesis_adjoint {ι : Type*} [Fintype ι] (w : ι → ℝ)
    (p : ι → CountablePairSpace) (q : CountablePairSpace) (i : ι) :
    (countableScalarPairSynthesis w p).adjoint q i =
      (Real.sqrt (w i) : ℂ) * inner ℂ (p i) q := by
  classical
  have hb : countableScalarPairSynthesis w p (PiLp.single 2 i 1) =
      (Real.sqrt (w i) : ℂ) • p i := by
    simp [countableScalarPairSynthesis_apply, PiLp.single_apply]
  have h := ContinuousLinearMap.adjoint_inner_right
    (countableScalarPairSynthesis w p) (PiLp.single 2 i 1) q
  simpa only [EuclideanSpace.inner_single_left, map_one, one_mul, hb,
    inner_smul_left, Complex.conj_ofReal] using h

theorem countableScalarPairSynthesis_gram {ι : Type*} [Fintype ι] (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (p : ι → CountablePairSpace) :
    (countableScalarPairSynthesis w p).comp (countableScalarPairSynthesis w p).adjoint =
      ∑ i, (w i : ℂ) • InnerProductSpace.rankOne ℂ (p i) (p i) := by
  apply ContinuousLinearMap.ext
  intro q
  simp only [ContinuousLinearMap.comp_apply, countableScalarPairSynthesis_apply,
    countableScalarPairSynthesis_adjoint, sum_apply, smul_apply, InnerProductSpace.rankOne_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← mul_assoc, weightRoot_mul (hw i), smul_smul]

theorem countableScalarPairSynthesis_norm_sq {ι : Type*} [Fintype ι] (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (p : ι → CountablePairSpace) (β : ℝ) (hβ : 0 ≤ β)
    (hQ : ∀ q : CountablePairSpace,
      (inner ℂ q ((∑ i, (w i : ℂ) • InnerProductSpace.rankOne ℂ (p i) (p i)) q)).re ≤
        β * ‖q‖^2) (f : EuclideanSpace ℂ ι) :
    ‖countableScalarPairSynthesis w p f‖^2 ≤ β * ‖f‖^2 := by
  let S := countableScalarPairSynthesis w p
  have ha : ‖S.adjoint (S f)‖^2 ≤ β * ‖S f‖^2 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), ContinuousLinearMap.adjoint_inner_left,
      RCLike.re_eq_complex_re]
    change (inner ℂ (S f) ((S.comp S.adjoint) (S f))).re ≤ _
    rw [countableScalarPairSynthesis_gram w hw p]
    exact hQ _
  have hc : ‖S f‖^2 ≤ ‖S.adjoint (S f)‖ * ‖f‖ := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), ← ContinuousLinearMap.adjoint_inner_left S f (S f)]
    exact re_inner_le_norm (𝕜 := ℂ) _ _
  have hc2 := (sq_le_sq₀ (sq_nonneg ‖S f‖)
    (mul_nonneg (norm_nonneg (S.adjoint (S f))) (norm_nonneg f))).mpr hc
  rw [mul_pow] at hc2
  have hh := mul_le_mul_of_nonneg_right ha (sq_nonneg ‖f‖)
  change ‖S f‖^2 ≤ β * ‖f‖^2
  by_cases hz : ‖S f‖ = 0
  · rw [hz, zero_pow (by decide)]
    exact mul_nonneg hβ (sq_nonneg _)
  · have hpos : 0 < ‖S f‖^2 := sq_pos_of_ne_zero hz
    nlinarith only [hc2, hh, hpos]

/-- The spectator-fiber identity for the actual finite tensor sum. -/
theorem countablePairTensor_sum_fiber {ι : Type*} [Fintype ι] (w : ι → ℝ)
    (p : ι → CountablePairSpace) (f : ι → CountableSpace) (A : Finset ℕ) :
    countablePairFiber (∑ i, (Real.sqrt (w i) : ℂ) • countablePairTensor (p i) (f i)) A =
      countableScalarPairSynthesis w p (WithLp.toLp 2 (fun i => f i A)) := by
  ext a
  simp only [countablePairFiber_apply, lp.coeFn_sum, lp.coeFn_smul, Finset.sum_apply,
    countablePairTensor_apply, countableScalarPairSynthesis_apply]
  change (∑ i, (Real.sqrt (w i) : ℂ) * (p i a * f i A)) =
    ∑ i, ((Real.sqrt (w i) : ℂ) * f i A) * p i a
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The same two-particle frame bound with an arbitrary completed system spectator.
The infinite sum exchange is justified by explicit HasSum proofs. -/
theorem countablePairTensor_synthesis_norm_sq {ι : Type*} [Fintype ι] (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (p : ι → CountablePairSpace) (β : ℝ) (hβ : 0 ≤ β)
    (hQ : ∀ q : CountablePairSpace,
      (inner ℂ q ((∑ i, (w i : ℂ) • InnerProductSpace.rankOne ℂ (p i) (p i)) q)).re ≤
        β * ‖q‖^2) (f : ι → CountableSpace) :
    ‖∑ i, (Real.sqrt (w i) : ℂ) • countablePairTensor (p i) (f i)‖^2 ≤
      β * ∑ i, ‖f i‖^2 := by
  let z := ∑ i, (Real.sqrt (w i) : ℂ) • countablePairTensor (p i) (f i)
  have hi (i : ι) : HasSum (fun A => ‖f i A‖^2) (‖f i‖^2) := by
    rw [l2_norm_sq]
    exact (l2_norm_sq_summable (f i)).hasSum
  have hr : HasSum (fun A => β * ∑ i, ‖f i A‖^2) (β * ∑ i, ‖f i‖^2) :=
    (hasSum_sum fun i (_ : i ∈ (Finset.univ : Finset ι)) => hi i).mul_left β
  have hl : Summable (fun A => ‖countablePairFiber z A‖^2) :=
    l2_norm_sq_summable (l2Exchange CountablePairIndex (Finset ℕ) z)
  rw [countablePairStackSpace_norm_sq]
  apply (hl.tsum_le_tsum (fun A => ?_) hr.summable).trans_eq hr.tsum_eq
  rw [countablePairTensor_sum_fiber]
  have h := countableScalarPairSynthesis_norm_sq w hw p β hβ hQ
    (WithLp.toLp 2 (fun i => f i A))
  simpa only [EuclideanSpace.norm_sq_eq, PiLp.toLp_apply] using h

end VortexGap.Fermion
