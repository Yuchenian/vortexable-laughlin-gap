import VortexGap.Frame.WeightedFrame

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped BigOperators InnerProduct ComplexConjugate

/-- A fixed system occupation leaves an ordinary l2 frame-label vector. -/
def frameFiber {n : ℕ} {ι : Type*} [Fintype ι] (A : Finset (Fin n)) :
    FrameStackSpace ι n →ₗ[ℂ] EuclideanSpace ℂ ι where
  toFun z := WithLp.toLp 2 (fun i => z (i,A))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem frameFiber_apply {n : ℕ} {ι : Type*} [Fintype ι]
    (A : Finset (Fin n)) (z : FrameStackSpace ι n) (i : ι) : frameFiber A z i = z (i,A) := rfl

theorem frameStack_norm_sq {n : ℕ} {ι : Type*} [Fintype ι] (z : FrameStackSpace ι n) :
    ‖z‖ ^ 2 = ∑ A : Finset (Fin n), ‖frameFiber A z‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, Finset.sum_comm]
  simp only [EuclideanSpace.norm_sq_eq]
  rfl

/-- The constructed S acts on labels and leaves the remaining Fock occupation unchanged. -/
def pairSynthesisStack {n : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (p : ι → PairSpace n) : FrameStackSpace ι n →ₗ[ℂ] PairStackSpace n where
  toFun z := WithLp.toLp 2 (fun aA => pairSynthesis w p (frameFiber aA.2 z) aA.1)
  map_add' x y := by ext aA; simp
  map_smul' z x := by ext aA; simp

theorem pairSynthesisStack_fiber {n : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (p : ι → PairSpace n) (z : FrameStackSpace ι n) (A : Finset (Fin n)) :
    pairFiber A (pairSynthesisStack w p z) = pairSynthesis w p (frameFiber A z) := rfl

theorem pairSynthesisStack_norm_sq_le {n : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (p : ι → PairSpace n) (β : ℝ) (hβ : 0 ≤ β)
    (hQ : ∀ q : PairSpace n,
      (inner ℂ q ((∑ i, (w i : ℂ) • pairRankOne (p i)) q)).re ≤ β * ‖q‖ ^ 2)
    (z : FrameStackSpace ι n) : ‖pairSynthesisStack w p z‖ ^ 2 ≤ β * ‖z‖ ^ 2 := by
  rw [pairStackSpace_norm_sq, frameStack_norm_sq, Finset.mul_sum]
  exact Finset.sum_le_sum fun A _ => pairSynthesis_norm_sq_le w hw p β hβ hQ (frameFiber A z)

/-- Insert the normalized two-particle environment state on each system fiber. -/
def pairEnvironmentEmbed {n : ℕ} : PairStackSpace n →ₗ[ℂ] SplitSpace n n where
  toFun z := WithLp.toLp 2 (fun AB => pairEmbed (pairFiber AB.2 z) AB.1)
  map_add' x y := by ext AB; simp
  map_smul' z x := by ext AB; simp

theorem pairEnvironmentEmbed_apply {n : ℕ} (z : PairStackSpace n)
    (A B : Finset (Fin n)) : pairEnvironmentEmbed z (A,B) = pairEmbed (pairFiber B z) A := rfl

theorem pairEnvironmentEmbed_norm_sq {n : ℕ} (z : PairStackSpace n) :
    ‖pairEnvironmentEmbed z‖ ^ 2 = ‖z‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, Finset.sum_comm, pairStackSpace_norm_sq]
  apply Finset.sum_congr rfl
  intro B _
  calc
    _ = ‖pairEmbed (pairFiber B z)‖ ^ 2 := (EuclideanSpace.norm_sq_eq _).symm
    _ = _ := by rw [pairEmbed_norm]

theorem pairEnvironmentEmbed_norm {n : ℕ} (z : PairStackSpace n) :
    ‖pairEnvironmentEmbed z‖ = ‖z‖ :=
  (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (pairEnvironmentEmbed_norm_sq z)

/-- The previously constructed CAR noise equals the actual E/S/analysis factorization. -/
theorem twoLossNoise_factorization {n : ℕ} {ι : Type*} [Fintype ι]
    (M : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (p : ι → PairSpace n) (x : Space n) :
    twoLossNoise M w p x =
      pairEnvironmentEmbed (pairAmplify (exteriorSquare (lossDefect M).toLinearMap)
        (pairSynthesisStack w p (frameAnalysis w (fun i => exteriorSquare M.toLinearMap (p i)) x))) := by
  have hf (B : Finset (Fin n)) :
      pairFiber B (pairSynthesisStack w p (frameAnalysis w (fun i => exteriorSquare M.toLinearMap (p i)) x)) =
      ∑ i, ((w i : ℂ) * pairAnnihilate (exteriorSquare M.toLinearMap (p i)) x B) • p i := by
    rw [pairSynthesisStack_fiber, pairSynthesis_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [frameFiber_apply, frameAnalysis_apply, ← mul_assoc, weightRoot_mul (hw i)]
  ext ⟨A,B⟩
  simp only [twoLossNoise, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    twoLossCreation, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul,
    fockProduct_apply, pairEnvironmentEmbed_apply, pairAmplify_fiber, hf,
    map_sum, map_smul]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Relative bound from raw Q, before replacing the genuine exterior-square norm by delta. -/
theorem twoLossNoise_exterior_bound {n : ℕ} {ι : Type*} [Fintype ι]
    (M : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (p : ι → PairSpace n) (β : ℝ) (hβ : 0 ≤ β)
    (hQ : ∀ q : PairSpace n,
      (inner ℂ q ((∑ i, (w i : ℂ) • pairRankOne (p i)) q)).re ≤ β * ‖q‖ ^ 2)
    (x : Space n) :
    ‖twoLossNoise M w p x‖ ^ 2 ≤
      β * ‖(exteriorSquare (lossDefect M).toLinearMap).toContinuousLinearMap‖ ^ 2 *
        (inner ℂ x (filteredHamiltonian M w p x)).re := by
  rw [twoLossNoise_factorization M w hw p x, pairEnvironmentEmbed_norm_sq]
  let z := frameAnalysis w (fun i => exteriorSquare M.toLinearMap (p i)) x
  have ha := pairAmplify_norm_le (exteriorSquare (lossDefect M).toLinearMap) (pairSynthesisStack w p z)
  have ha2 := (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr ha
  rw [mul_pow] at ha2
  have hs := mul_le_mul_of_nonneg_left (pairSynthesisStack_norm_sq_le w hw p β hβ hQ z)
    (sq_nonneg ‖(exteriorSquare (lossDefect M).toLinearMap).toContinuousLinearMap‖)
  have hz := filtered_frameAnalysis_norm_sq M w hw p x
  change ‖z‖ ^ 2 = _ at hz
  calc
    _ ≤ ‖(exteriorSquare (lossDefect M).toLinearMap).toContinuousLinearMap‖ ^ 2 * (β * ‖z‖ ^ 2) := ha2.trans hs
    _ = _ := by rw [hz]; ring

end VortexGap.Fermion
