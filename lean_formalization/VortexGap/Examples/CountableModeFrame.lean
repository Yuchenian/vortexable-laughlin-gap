import VortexGap.Examples.CountableCellReference
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open VortexGap.Frame
open scoped BigOperators InnerProduct ComplexConjugate ComplexOrder ENNReal

def countableModeFrameMap (a : CountablePairIndex) : TwoSpace →ₗ[ℂ] CountableOrbital where
  toFun x := x 0 • orbitalKet a.val.1 + x 1 • orbitalKet a.val.2
  map_add' x y := by simp only [PiLp.add_apply, add_smul]; abel
  map_smul' z x := by simp only [PiLp.smul_apply, smul_eq_mul, smul_add, smul_smul, RingHom.id_apply]

theorem countableModeFrameMap_inner (a : CountablePairIndex) (x y : TwoSpace) :
    inner ℂ (countableModeFrameMap a x) (countableModeFrameMap a y) = inner ℂ x y := by
  change inner ℂ (x 0 • orbitalKet a.val.1 + x 1 • orbitalKet a.val.2)
    (y 0 • orbitalKet a.val.1 + y 1 • orbitalKet a.val.2) = _
  simp [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    orbitalKet_inner_left, orbitalKet, lp.inner_single_left, lp.single_apply, ne_of_lt a.property,
    ne_of_gt a.property, PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, mul_comm]

def countableModeFrame (a : CountablePairIndex) : CountableTwoFrame where
  toLinearMap := countableModeFrameMap a
  norm_map' := (LinearMap.norm_map_iff_inner_map_map _).mpr (countableModeFrameMap_inner a)

theorem countableModeFrame_first (a : CountablePairIndex) :
    countableModeFrame a (PiLp.single 2 0 1) = orbitalKet a.val.1 := by
  change (PiLp.single 2 0 (1 : ℂ) : TwoSpace) 0 • orbitalKet a.val.1 +
    (PiLp.single 2 0 (1 : ℂ) : TwoSpace) 1 • orbitalKet a.val.2 = _
  simp

theorem countableModeFrame_second (a : CountablePairIndex) :
    countableModeFrame a (PiLp.single 2 1 1) = orbitalKet a.val.2 := by
  change (PiLp.single 2 1 (1 : ℂ) : TwoSpace) 0 • orbitalKet a.val.1 +
    (PiLp.single 2 1 (1 : ℂ) : TwoSpace) 1 • orbitalKet a.val.2 = _
  simp

theorem countableTwoFrameOverlap_self (U : CountableTwoFrame) :
    countableTwoFrameOverlap U U = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  change inner ℂ y (U.toContinuousLinearMap.adjoint (U x)) = inner ℂ y x
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact U.inner_map_map y x

theorem countableModePair_norm (a : CountablePairIndex) :
    ‖(lp.single 2 a 1 : CountablePairSpace)‖ = 1 := by
  simp [lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]

theorem countableModePair_bound (a : CountablePairIndex) (q : CountablePairSpace) :
    (inner ℂ q (InnerProductSpace.rankOne ℂ
      (lp.single 2 a 1) (lp.single 2 a 1) q)).re ≤ 1 * ‖q‖^2 := by
  let Q := InnerProductSpace.rankOne ℂ (lp.single 2 a 1 : CountablePairSpace) (lp.single 2 a 1 : CountablePairSpace)
  have hn : ‖Q‖ = 1 := by simp [Q, countableModePair_norm]
  calc
    _ ≤ ‖q‖ * ‖Q q‖ := re_inner_le_norm (𝕜 := ℂ) q (Q q)
    _ ≤ ‖q‖ * (‖Q‖ * ‖q‖) := mul_le_mul_of_nonneg_left (Q.le_opNorm q) (norm_nonneg q)
    _ = _ := by rw [hn]; ring

/-- Raw frame and original gap data are all discharged; M is still arbitrary. -/
theorem countable_single_pair_transfer (a : CountablePairIndex)
    (M : CountableOrbital →L[ℂ] CountableOrbital) (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1)
    (N : ℕ) :
    let p := countableWedge (M (orbitalKet a.val.1)) (M (orbitalKet a.val.2))
    let H := countablePairLift N (InnerProductSpace.rankOne ℂ p p)
    (H*H - ((1-2*‖1-M^2‖-‖1-M^2‖^2 : ℝ) : ℂ) • H).IsPositive := by
  have hrow : ∀ i : Unit, ∑ j : Unit, (1 : ℝ) *
      traceNormTwo (countableTwoFrameOverlap (countableModeFrame a) (countableModeFrame a)) * 1 ≤ 2*1 := by
    intro i
    simp [countableTwoFrameOverlap_self, traceNormTwo_id]
  have hQ : ∀ q : CountablePairSpace,
      (inner ℂ q ((countableFramePair Finset.univ (fun _ : Unit => (1 : ℂ))
        (fun _ => countableModeFrame a (PiLp.single 2 0 1))
        (fun _ => countableModeFrame a (PiLp.single 2 1 1))) q)).re ≤ 1*‖q‖^2 := by
    intro q
    simpa [countableFramePair, countableModeFrame_first, countableModeFrame_second,
      countableWedge_basis] using countableModePair_bound a q
  have hgap : ∀ k ≤ N,
      let H := countablePairLift k (countableFramePair Finset.univ (fun _ : Unit => (1 : ℂ))
        (fun _ => countableModeFrame a (PiLp.single 2 0 1))
        (fun _ => countableModeFrame a (PiLp.single 2 1 1)))
      (H*H - (1 : ℂ) • H).IsPositive := by
    intro k hk
    simpa [countableFramePair, countableModeFrame_first, countableModeFrame_second,
      countableWedge_basis] using countableModePairLift_gap a k
  have h := countable_finite_frame_transfer M hM hc (fun _ : Unit => 1) (by intro; norm_num)
    (fun _ => countableModeFrame a) (fun _ => 1) (by intro; norm_num)
    2 hrow 1 (by norm_num) hQ 1 N hgap
  simpa [countableFramePair, countableModeFrame_first, countableModeFrame_second] using h
end VortexGap.Fermion
