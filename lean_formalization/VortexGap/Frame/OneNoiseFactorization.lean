import VortexGap.Frame.TwoFrameOverlap
import VortexGap.Frame.WeightedSchur

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open VortexGap.Frame
open scoped BigOperators InnerProduct ComplexConjugate

/-- Select one label from the ordinary l2 frame/Fock product. -/
def frameSlice {n : ℕ} {ι : Type*} [Fintype ι] (i : ι) : FrameStackSpace ι n →ₗ[ℂ] Space n where
  toFun z := WithLp.toLp 2 (fun A => z (i,A))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem frameSlice_apply {n : ℕ} {ι : Type*} [Fintype ι]
    (i : ι) (z : FrameStackSpace ι n) (A : Finset (Fin n)) : frameSlice i z A = z (i,A) := rfl

theorem frameStack_norm_sq_labels {n : ℕ} {ι : Type*} [Fintype ι] (z : FrameStackSpace ι n) :
    ‖z‖^2 = ∑ i, ‖frameSlice i z‖^2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  simp only [EuclideanSpace.norm_sq_eq, frameSlice_apply]

theorem frameSlice_analysis {n : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (p : ι → PairSpace n) (x : Space n) (i : ι) :
    frameSlice i (frameAnalysis w p x) = (Real.sqrt (w i) : ℂ) • pairAnnihilate (p i) x := by
  ext A
  simp only [frameSlice_apply, frameAnalysis_apply, PiLp.smul_apply, smul_eq_mul]

/-- Weighted synthesis of the actual mixed CAR columns. -/
def oneFrameSynthesis {n : ℕ} {ι : Type*} [Fintype ι]
    (M : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (w : ι → ℝ) (u v : ι → EuclideanSpace ℂ (Fin n)) :
    FrameStackSpace ι n →ₗ[ℂ] OrbitalStackSpace n where
  toFun z := ∑ i, (Real.sqrt (w i) : ℂ) • oneFrameCreation M (u i) (v i) (frameSlice i z)
  map_add' x y := by simp [smul_add, Finset.sum_add_distrib]
  map_smul' z x := by
    simp only [map_smul, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact smul_comm _ _ _

theorem oneFrameSynthesis_apply {n : ℕ} {ι : Type*} [Fintype ι]
    (M : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (w : ι → ℝ) (u v : ι → EuclideanSpace ℂ (Fin n)) (z : FrameStackSpace ι n) :
    oneFrameSynthesis M w u v z =
      ∑ i, (Real.sqrt (w i) : ℂ) • oneFrameCreation M (u i) (v i) (frameSlice i z) := rfl

theorem oneFrameSynthesis_analysis {n : ℕ} {ι : Type*} [Fintype ι]
    (M : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (u v : ι → EuclideanSpace ℂ (Fin n))
    (p : ι → PairSpace n) (x : Space n) :
    oneFrameSynthesis M w u v (frameAnalysis w p x) =
      ∑ i, (w i : ℂ) • oneFrameCreation M (u i) (v i) (pairAnnihilate (p i) x) := by
  rw [oneFrameSynthesis_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [frameSlice_analysis, map_smul, smul_smul, weightRoot_mul (hw i)]

theorem oneLossNoise_factorization {n : ℕ} {ι : Type*} [Fintype ι]
    (M : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (u v : ι → EuclideanSpace ℂ (Fin n)) (x : Space n) :
    oneLossNoise M w u v x =
      orbitalEnvironmentEmbed (orbitalAmplify (lossDefect M)
        (oneFrameSynthesis M w u v
          (frameAnalysis w (fun i => exteriorSquare M.toLinearMap (wedgePair (u i) (v i))) x))) := by
  rw [oneFrameSynthesis_analysis M w hw u v]
  simp only [oneLossNoise, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    map_sum, map_smul, oneLossCreation_factorization]

/-- Schur applied to the actual Gram norms, whose symmetry follows from the adjoint.
The sole row hypothesis is the original one-particle trace-norm Schur condition. -/
theorem oneFrameSynthesis_norm_sq_le {n : ℕ} {ι : Type*} [Fintype ι]
    (M : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) (hc : ‖M‖ ≤ 1)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (U : ι → TwoFrame n)
    (ω : ι → ℝ) (hω : ∀ i, 0 < ω i) (C : ℝ)
    (hrow : ∀ i, ∑ j, w j * traceNormTwo (twoFrameOverlap (U i) (U j)) * ω j ≤ C * ω i)
    (z : FrameStackSpace ι n) :
    ‖oneFrameSynthesis M w (fun i => U i (PiLp.single 2 0 1))
      (fun i => U i (PiLp.single 2 1 1)) z‖^2 ≤ C * ‖z‖^2 := by
  let R (i : ι) := (oneFrameCreation M (U i (PiLp.single 2 0 1))
    (U i (PiLp.single 2 1 1))).toContinuousLinearMap
  let k (i j : ι) : ℝ := ‖(R i).adjoint ∘L R j‖
  have hk (i j : ι) : 0 ≤ k i j := norm_nonneg _
  have hs (i j : ι) : k i j = k j i := by
    have h := ContinuousLinearMap.adjoint.norm_map ((R i).adjoint ∘L R j)
    simpa only [k, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint] using h.symm
  have hr (i : ι) : ∑ j, w j * k i j * ω j ≤ C * ω i := by
    apply le_trans (Finset.sum_le_sum fun j _ => ?_) (hrow i)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (twoFrame_overlap_norm_le M hc (U i) (U j)) (hw j)) (le_of_lt (hω j))
  have h := finite_weighted_synthesis_norm_sq R w hw ω hω k C hk hs hr
    (fun _ _ => le_refl _) (fun i => frameSlice i z)
  rw [← frameStack_norm_sq_labels] at h
  exact h

end VortexGap.Fermion
