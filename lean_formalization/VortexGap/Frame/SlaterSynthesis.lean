import VortexGap.Transfer.FiniteFrame
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open VortexGap.Frame
open scoped InnerProduct ComplexConjugate

variable {n : ℕ} {α : Type*} [Fintype α]

def slaterPair (c : α → ℂ) (U : α → TwoFrame n) : PairSpace n :=
  ∑ a, c a • wedgePair (U a (PiLp.single 2 0 1)) (U a (PiLp.single 2 1 1))

def slaterColumn (M : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (c : α → ℂ) (U : α → TwoFrame n) : Space n →L[ℂ] OrbitalStackSpace n :=
  ∑ a, c a • (oneFrameCreation M (U a (PiLp.single 2 0 1)) (U a (PiLp.single 2 1 1))).toContinuousLinearMap

def slaterKernel (c d : α → ℂ) (U V : α → TwoFrame n) : ℝ :=
  ∑ a, ∑ b, ‖c a‖ * ‖d b‖ * traceNormTwo (twoFrameOverlap (U a) (V b))

theorem sumColumn_gram {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (R S : α → E →L[ℂ] F) (c d : α → ℂ) :
    ‖(∑ a, c a • R a).adjoint ∘L (∑ b, d b • S b)‖ ≤
      ∑ a, ∑ b, ‖c a‖ * ‖d b‖ * ‖(R a).adjoint ∘L S b‖ := by
  rw [map_sum, ContinuousLinearMap.finsetSum_comp]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro a _
  rw [ContinuousLinearMap.comp_finsetSum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro b _
  rw [map_smulₛₗ, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul,
    norm_smul, norm_smul, mul_assoc]
  simp

theorem slaterColumn_gram_le (M : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (hc : ‖M‖ ≤ 1) (c d : α → ℂ) (U V : α → TwoFrame n) :
    ‖(slaterColumn M c U).adjoint ∘L slaterColumn M d V‖ ≤ slaterKernel c d U V := by
  apply (sumColumn_gram _ _ c d).trans
  apply Finset.sum_le_sum
  intro a _
  apply Finset.sum_le_sum
  intro b _
  exact mul_le_mul_of_nonneg_left (twoFrame_overlap_norm_le M hc (U a) (V b))
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))

theorem slater_synthesis_le {ι : Type*} [Fintype ι]
    (M : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) (hc : ‖M‖ ≤ 1)
    (c : ι → α → ℂ) (U : ι → α → TwoFrame n) (w ω : ι → ℝ) (C : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hω : ∀ i, 0 < ω i)
    (hrow : ∀ i, ∑ j, w j * slaterKernel (c i) (c j) (U i) (U j) * ω j ≤ C*ω i)
    (z : ι → Space n) :
    ‖∑ i, (Real.sqrt (w i):ℂ) • slaterColumn M (c i) (U i) (z i)‖^2 ≤ C * ∑ i, ‖z i‖^2 := by
  let R := fun i => slaterColumn M (c i) (U i)
  let k := fun i j => ‖(R i).adjoint ∘L R j‖
  have hs (i j : ι) : k i j = k j i := by
    have h := ContinuousLinearMap.adjoint.norm_map ((R i).adjoint ∘L R j)
    simpa only [k, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint] using h.symm
  apply finite_weighted_synthesis_norm_sq R w hw ω hω k C (fun _ _ => norm_nonneg _) hs _ (fun _ _ => le_rfl) z
  intro i
  apply le_trans (Finset.sum_le_sum fun j _ => ?_) (hrow i)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (slaterColumn_gram_le M hc _ _ _ _) (hw j)) (hω j).le

variable {ι : Type*} [Fintype ι]
variable (M : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
variable (w : ι → ℝ) (c : ι → α → ℂ) (U : ι → α → TwoFrame n)

def slaterOneNoise : Space n →ₗ[ℂ] SplitSpace n n :=
  ∑ i, (w i:ℂ) • (∑ a, c i a • oneLossCreation M
    (U i a (PiLp.single 2 0 1)) (U i a (PiLp.single 2 1 1))).comp
      (pairAnnihilate (exteriorSquare M.toLinearMap (slaterPair (c i) (U i))))

theorem slaterOneNoise_factor (hw : ∀ i, 0 ≤ w i) (x : Space n) :
    let z := frameAnalysis w (fun i => exteriorSquare M.toLinearMap (slaterPair (c i) (U i))) x
    slaterOneNoise M w c U x = orbitalEnvironmentEmbed (orbitalAmplify (lossDefect M)
      (∑ i, (Real.sqrt (w i):ℂ) • slaterColumn M (c i) (U i) (frameSlice i z))) := by
  dsimp only
  simp only [slaterOneNoise, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    frameSlice_analysis, map_smul, smul_smul, weightRoot_mul (hw _), map_sum]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  simp only [slaterColumn, ContinuousLinearMap.sum_apply, smul_apply, map_sum, map_smul,
    oneLossCreation_factorization]
  rfl

theorem slaterOneNoise_relative (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1) (hw : ∀ i, 0 ≤ w i)
    (ω : ι → ℝ) (hω : ∀ i, 0 < ω i) (C : ℝ)
    (hrow : ∀ i, ∑ j, w j * slaterKernel (c i) (c j) (U i) (U j) * ω j ≤ C*ω i) (x : Space n) :
    ‖slaterOneNoise M w c U x‖^2 ≤ C*‖1-M^2‖*
      (inner ℂ x (filteredHamiltonian M w (fun i => slaterPair (c i) (U i)) x)).re := by
  let z := frameAnalysis w (fun i => exteriorSquare M.toLinearMap (slaterPair (c i) (U i))) x
  let r := ∑ i, (Real.sqrt (w i):ℂ) • slaterColumn M (c i) (U i) (frameSlice i z)
  rw [slaterOneNoise_factor M w c U hw, orbitalEnvironmentEmbed_norm_sq]
  have ha := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
    (orbitalAmplify_norm_le (lossDefect M) r)
  rw [mul_pow] at ha
  have hs := slater_synthesis_le M hc c U w ω C hw hω hrow (fun i => frameSlice i z)
  rw [← frameStack_norm_sq_labels] at hs
  have hz := filtered_frameAnalysis_norm_sq M w hw (fun i => slaterPair (c i) (U i)) x
  calc
    _ ≤ ‖lossDefect M‖^2*‖r‖^2 := ha
    _ ≤ ‖lossDefect M‖^2*(C*‖z‖^2) := mul_le_mul_of_nonneg_left hs (sq_nonneg _)
    _ = _ := by rw [lossDefect_norm_sq M hM hc]; dsimp only [z]; rw [hz]; ring

end VortexGap.Fermion
