import VortexGap.Frame.CountablePairSynthesis
import VortexGap.Frame.CountableOneNoise
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped BigOperators InnerProduct ComplexOrder

theorem countablePairTensor_smul_right (p : CountablePairSpace) (c : ℂ) (x : CountableSpace) :
    countablePairTensor p (c • x) = c • countablePairTensor p x := by
  ext a A
  change p a * (c * x A) = c * (p a * x A)
  ring

theorem countableFrameNoiseTwo_factorization {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    (M : CountableOrbital →L[ℂ] CountableOrbital) (u v : ι → CountableOrbital)
    (N : ℕ) (x : countableSector N) :
    countableFrameNoiseTwo s a M u v N x =
      countablePairEnvironmentEmbed
        (countablePairAmplify (countablePairFilter (lossDefect M) (lossDefect_nonneg M))
          (∑ i ∈ s, a i • countablePairTensor (countableWedge (u i) (v i))
            (countablePairAnnihilate N (countableWedge (M (u i)) (M (v i))) x))) := by
  simp only [countableFrameNoiseTwo, sum_apply, smul_apply, ContinuousLinearMap.comp_apply,
    countableLossCreationTwo_factorization, map_sum, map_smul]

theorem countablePairEnvironment_filter_norm_sq
    (M : CountableOrbital →L[ℂ] CountableOrbital) (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1)
    (z : CountablePairStackSpace) :
    ‖countablePairEnvironmentEmbed
      (countablePairAmplify (countablePairFilter (lossDefect M) (lossDefect_nonneg M)) z)‖^2 ≤
      ‖1-M^2‖^2 * ‖z‖^2 := by
  have h : ‖countablePairEnvironmentEmbed
      (countablePairAmplify (countablePairFilter (lossDefect M) (lossDefect_nonneg M)) z)‖ ≤
      ‖lossDefect M‖^2 * ‖z‖ := by
    exact (countablePairEnvironmentEmbed_norm_le _).trans
      ((countablePairAmplify_norm_le _ _).trans
        (mul_le_mul_of_nonneg_right (countablePairFilter_norm_le _ _) (norm_nonneg z)))
  have hsq := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (sq_nonneg _) (norm_nonneg z))).mpr h
  simpa only [mul_pow, lossDefect_norm_sq M hM hc] using hsq

/-- Second relative noise bound from the raw two-particle frame bound.
No two-environment norm premise is supplied. -/
theorem countableFrameNoiseTwo_relative {ι : Type*} [Fintype ι]
    (M : CountableOrbital →L[ℂ] CountableOrbital) (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (u v : ι → CountableOrbital)
    (β : ℝ) (hβ : 0 ≤ β)
    (hQ : ∀ q : CountablePairSpace,
      (inner ℂ q (countableFramePair Finset.univ (fun i => (w i : ℂ)) u v q)).re ≤ β * ‖q‖^2)
    (N : ℕ) (x : countableSector N) :
    ‖countableFrameNoiseTwo Finset.univ (fun i => (w i : ℂ)) M u v N x‖^2 ≤
      β * ‖1-M^2‖^2 * (inner ℂ x (countablePairLift N
        (countableFramePair Finset.univ (fun i => (w i : ℂ))
          (fun i => M (u i)) (fun i => M (v i))) x)).re := by
  let p := fun i => countableWedge (u i) (v i)
  let b := fun i => countablePairAnnihilate N (countableWedge (M (u i)) (M (v i))) x
  let z := ∑ i, (w i : ℂ) • countablePairTensor (p i) (b i)
  have he : (∑ i, (Real.sqrt (w i) : ℂ) • countablePairTensor (p i)
      ((Real.sqrt (w i) : ℂ) • b i)) = z := by
    simp only [countablePairTensor_smul_right, smul_smul, weightRoot_mul (hw _)]
    rfl
  have hn (i : ι) : ‖(Real.sqrt (w i) : ℂ) • b i‖^2 = w i * ‖b i‖^2 := by
    rw [norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hw i)]
  have hs := countablePairTensor_synthesis_norm_sq w hw p β hβ hQ
    (fun i => (Real.sqrt (w i) : ℂ) • b i)
  rw [he] at hs
  simp only [hn] at hs
  rw [countableFrameNoiseTwo_factorization, countableFramePair_energy]
  change ‖countablePairEnvironmentEmbed
    (countablePairAmplify (countablePairFilter (lossDefect M) (lossDefect_nonneg M)) z)‖^2 ≤
      β * ‖1-M^2‖^2 * ∑ i, w i * ‖b i‖^2
  calc
    _ ≤ ‖1-M^2‖^2 * ‖z‖^2 := countablePairEnvironment_filter_norm_sq M hM hc z
    _ ≤ ‖1-M^2‖^2 * (β * ∑ i, w i * ‖b i‖^2) :=
      mul_le_mul_of_nonneg_left hs (sq_nonneg _)
    _ = _ := by ring
end VortexGap.Fermion
