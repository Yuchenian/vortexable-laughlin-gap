import VortexGap.Fermion.CountableOneEnvironment
import VortexGap.Fermion.CountableFrameLossOutput
import VortexGap.Frame.CountableTwoFrameOverlap
import VortexGap.Frame.WeightedSchur
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open VortexGap.Frame
open scoped BigOperators InnerProduct ComplexOrder

theorem countableFramePair_energy {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (u v : ι → CountableOrbital) (N : ℕ) (x : countableSector N) :
    (inner ℂ x (countablePairLift N (countableFramePair s (fun i => (w i : ℂ)) u v) x)).re =
      ∑ i ∈ s, w i * ‖countablePairAnnihilate N (countableWedge (u i) (v i)) x‖^2 := by
  simp only [countableFramePair, countablePairLift_sum, sum_apply, inner_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [countablePairLift_smul]
  have h : inner ℂ x ((w i : ℂ) • (countablePairLift N
      (InnerProductSpace.rankOne ℂ (countableWedge (u i) (v i))
        (countableWedge (u i) (v i))) x)) =
      (w i : ℂ) * inner ℂ x (countablePairLift N
        (InnerProductSpace.rankOne ℂ (countableWedge (u i) (v i))
          (countableWedge (u i) (v i))) x) :=
    inner_smul_right (𝕜 := ℂ) x _ (w i : ℂ)
  calc
    _ = ((w i : ℂ) * inner ℂ x (countablePairLift N
        (InnerProductSpace.rankOne ℂ (countableWedge (u i) (v i))
          (countableWedge (u i) (v i))) x)).re := congrArg Complex.re h
    _ = _ := by
      rw [countablePairLift_rankOne, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
      simp [← Complex.ofReal_pow]

theorem countableOneFrame_synthesis_norm_sq {ι : Type*} [Fintype ι]
    (M : CountableOrbital →L[ℂ] CountableOrbital) (hc : ‖M‖ ≤ 1)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (U : ι → CountableTwoFrame)
    (ω : ι → ℝ) (hω : ∀ i, 0 < ω i) (C : ℝ)
    (hrow : ∀ i, ∑ j, w j * traceNormTwo (countableTwoFrameOverlap (U i) (U j)) * ω j ≤ C * ω i)
    (f : ι → CountableSpace) :
    ‖∑ i, (Real.sqrt (w i) : ℂ) • countableOneFrameCreation M
      (U i (PiLp.single 2 0 1)) (U i (PiLp.single 2 1 1)) (f i)‖^2 ≤
      C * ∑ i, ‖f i‖^2 := by
  let R (i : ι) := countableOneFrameCreation M (U i (PiLp.single 2 0 1))
    (U i (PiLp.single 2 1 1))
  let k (i j : ι) : ℝ := ‖(R i).adjoint ∘L R j‖
  have hk (i j : ι) : 0 ≤ k i j := norm_nonneg _
  have hs (i j : ι) : k i j = k j i := by
    have h := ContinuousLinearMap.adjoint.norm_map ((R i).adjoint ∘L R j)
    simpa only [k, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint] using h.symm
  have hr (i : ι) : ∑ j, w j * k i j * ω j ≤ C * ω i := by
    apply le_trans (Finset.sum_le_sum fun j _ => ?_) (hrow i)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (countableTwoFrame_overlap_norm_le M hc (U i) (U j))
        (hw j)) (le_of_lt (hω j))
  exact finite_weighted_synthesis_norm_sq R w hw ω hω k C hk hs hr (fun _ _ => le_refl _) f

theorem countableFrameNoiseOne_factorization {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    (M : CountableOrbital →L[ℂ] CountableOrbital) (u v : ι → CountableOrbital)
    (N : ℕ) (x : countableSector N) :
    countableFrameNoiseOne s a M u v N x =
      countableOneEnvironmentAction (lossDefect M)
        (∑ i ∈ s, a i • countableOneFrameCreation M (u i) (v i)
          (countablePairAnnihilate N (countableWedge (M (u i)) (M (v i))) x)) := by
  simp only [countableFrameNoiseOne, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    countableLossCreationOne_factorization, map_sum, map_smul]

/-- First relative noise bound on complete countable-mode fixed-N sectors.
All noise and Gram data are derived from the concrete CAR construction. -/
theorem countableFrameNoiseOne_relative {ι : Type*} [Fintype ι]
    (M : CountableOrbital →L[ℂ] CountableOrbital) (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (U : ι → CountableTwoFrame)
    (ω : ι → ℝ) (hω : ∀ i, 0 < ω i) (C : ℝ)
    (hrow : ∀ i, ∑ j, w j * traceNormTwo (countableTwoFrameOverlap (U i) (U j)) * ω j ≤ C * ω i)
    (N : ℕ) (x : countableSector N) :
    ‖countableFrameNoiseOne Finset.univ (fun i => (w i : ℂ)) M
      (fun i => U i (PiLp.single 2 0 1)) (fun i => U i (PiLp.single 2 1 1)) N x‖^2 ≤
      C * ‖1-M^2‖ * (inner ℂ x (countablePairLift N
        (countableFramePair Finset.univ (fun i => (w i : ℂ))
          (fun i => M (U i (PiLp.single 2 0 1)))
          (fun i => M (U i (PiLp.single 2 1 1)))) x)).re := by
  let u := fun i => U i (PiLp.single 2 0 1)
  let v := fun i => U i (PiLp.single 2 1 1)
  let b := fun i => countablePairAnnihilate N (countableWedge (M (u i)) (M (v i))) x
  let r : CountableSpace := ∑ i, (w i : ℂ) • countableOneFrameCreation M (u i) (v i) (b i)
  have he : (∑ i, (Real.sqrt (w i) : ℂ) • countableOneFrameCreation M
      (u i) (v i) ((Real.sqrt (w i) : ℂ) • b i)) = r := by
    simp only [map_smul, smul_smul, weightRoot_mul (hw _)]
    rfl
  have hn (i : ι) : ‖(Real.sqrt (w i) : ℂ) • b i‖^2 = w i * ‖b i‖^2 := by
    rw [norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hw i)]
  have hs := countableOneFrame_synthesis_norm_sq M hc w hw U ω hω C hrow
    (fun i => (Real.sqrt (w i) : ℂ) • b i)
  change ‖∑ i, (Real.sqrt (w i) : ℂ) • countableOneFrameCreation M (u i) (v i)
    ((Real.sqrt (w i) : ℂ) • b i)‖^2 ≤ _ at hs
  rw [he] at hs
  simp only [hn] at hs
  rw [countableFrameNoiseOne_factorization, countableFramePair_energy]
  change ‖countableOneEnvironmentAction (lossDefect M) r‖^2 ≤
    C * ‖1-M^2‖ * ∑ i, w i * ‖b i‖^2
  have ha := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
    (countableOneEnvironmentAction_norm_le (lossDefect M) r)
  rw [mul_pow] at ha
  calc
    _ ≤ ‖lossDefect M‖^2 * ‖r‖^2 := ha
    _ ≤ ‖lossDefect M‖^2 * (C * ∑ i, w i * ‖b i‖^2) :=
      mul_le_mul_of_nonneg_left hs (sq_nonneg _)
    _ = _ := by rw [lossDefect_norm_sq M hM hc]; ring
end VortexGap.Fermion
