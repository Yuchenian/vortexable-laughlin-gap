import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Tactic

/-! The loss defect is constructed by positive functional calculus, not postulated. -/
noncomputable section
set_option autoImplicit false
namespace VortexGap
open scoped InnerProduct ComplexOrder
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def lossDefect (M : H →L[ℂ] H) : H →L[ℂ] H := CFC.sqrt (1 - M ^ 2)

theorem lossDefect_nonneg (M : H →L[ℂ] H) : 0 ≤ lossDefect M := CFC.sqrt_nonneg _

theorem loss_input_nonneg (M : H →L[ℂ] H) (hM : 0 ≤ M) (hcontract : ‖M‖ ≤ 1) :
    0 ≤ 1 - M ^ 2 := by
  have hself : IsSelfAdjoint M := IsSelfAdjoint.of_nonneg hM
  have hs : 0 ≤ M ^ 2 := by cfc_tac
  rw [sub_nonneg, ← CStarAlgebra.norm_le_one_iff_of_nonneg (M ^ 2) hs,
    pow_two, hself.norm_mul_self]
  exact (sq_le_one_iff₀ (norm_nonneg M)).mpr hcontract

theorem lossDefect_square (M : H →L[ℂ] H) (hM : 0 ≤ M) (hcontract : ‖M‖ ≤ 1) :
    lossDefect M * lossDefect M = 1 - M ^ 2 :=
  CFC.sqrt_mul_sqrt_self _ (loss_input_nonneg M hM hcontract)

theorem lossDefect_complete (M : H →L[ℂ] H) (hM : 0 ≤ M) (hcontract : ‖M‖ ≤ 1) :
    lossDefect M * lossDefect M + M * M = 1 := by
  rw [lossDefect_square M hM hcontract, pow_two, sub_add_cancel]

theorem lossDefect_commute (M : H →L[ℂ] H) : Commute (lossDefect M) M := by
  have h : Commute (1 - M ^ 2) M :=
    (Commute.one_left M).sub_left ((Commute.refl M).pow_left 2)
  simpa only [lossDefect, CFC.sqrt_eq_cfc] using h.cfc_nnreal NNReal.sqrt

/-- Both sides use the induced Hilbert operator norm. -/
theorem lossDefect_norm_sq (M : H →L[ℂ] H) (hM : 0 ≤ M) (hcontract : ‖M‖ ≤ 1) :
    ‖lossDefect M‖ ^ 2 = ‖1 - M ^ 2‖ := by
  rw [lossDefect, CFC.norm_sqrt _ (loss_input_nonneg M hM hcontract),
    Real.sq_sqrt (norm_nonneg _)]

theorem lossDefect_inner (M : H →L[ℂ] H) (hM : 0 ≤ M) (hcontract : ‖M‖ ≤ 1)
    (x y : H) :
    inner ℂ (lossDefect M x) (lossDefect M y) + inner ℂ (M x) (M y) = inner ℂ x y := by
  have hE : (lossDefect M).adjoint = lossDefect M :=
    (IsSelfAdjoint.of_nonneg (lossDefect_nonneg M)).star_eq
  have hMs : M.adjoint = M := (IsSelfAdjoint.of_nonneg hM).star_eq
  rw [← ContinuousLinearMap.adjoint_inner_right (lossDefect M), hE,
    ← ContinuousLinearMap.adjoint_inner_right M, hMs, ← inner_add_right]
  change inner ℂ x ((lossDefect M * lossDefect M + M * M) y) = _
  rw [lossDefect_complete M hM hcontract]
  rfl

abbrev Doubled (H : Type*) := WithLp 2 (H × H)

def lossEmbeddingLinear (M : H →L[ℂ] H) : H →ₗ[ℂ] Doubled H where
  toFun x := WithLp.toLp 2 (lossDefect M x, M x)
  map_add' x y := by apply WithLp.ofLp_injective 2; ext <;> simp
  map_smul' z x := by apply WithLp.ofLp_injective 2; ext <;> simp

def lossEmbedding (M : H →L[ℂ] H) (hM : 0 ≤ M) (hcontract : ‖M‖ ≤ 1) :
    H →ₗᵢ[ℂ] Doubled H :=
  (lossEmbeddingLinear M).isometryOfInner (fun x y => lossDefect_inner M hM hcontract x y)

theorem lossEmbedding_gram (M : H →L[ℂ] H) (hM : 0 ≤ M) (hcontract : ‖M‖ ≤ 1) :
    (lossEmbedding M hM hcontract).toContinuousLinearMap.adjoint ∘L
      (lossEmbedding M hM hcontract).toContinuousLinearMap = 1 :=
  (lossEmbedding M hM hcontract).adjoint_comp_self

/-- Environment coordinate first, with the Hilbert l2 product norm. -/
def lossRotationLinear (M : H →L[ℂ] H) : Doubled H →ₗ[ℂ] Doubled H where
  toFun z := WithLp.toLp 2
    (lossDefect M z.fst + M z.snd, M z.fst - lossDefect M z.snd)
  map_add' z w := by apply WithLp.ofLp_injective 2; ext <;> simp <;> abel
  map_smul' a z := by apply WithLp.ofLp_injective 2; ext <;> simp [smul_add, smul_sub]

theorem lossRotation_involutive (M : H →L[ℂ] H) (hM : 0 ≤ M) (hcontract : ‖M‖ ≤ 1) :
    Function.Involutive (lossRotationLinear M) := by
  have hs (x : H) : lossDefect M (lossDefect M x) + M (M x) = x :=
    congrArg (fun T : H →L[ℂ] H => T x) (lossDefect_complete M hM hcontract)
  have hc (x : H) : lossDefect M (M x) = M (lossDefect M x) :=
    congrArg (fun T : H →L[ℂ] H => T x) (lossDefect_commute M).eq
  intro z
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · change lossDefect M (lossDefect M z.fst + M z.snd) +
        M (M z.fst - lossDefect M z.snd) = z.fst
    simp only [map_add, map_sub, hc]
    calc
      _ = lossDefect M (lossDefect M z.fst) + M (M z.fst) := by abel
      _ = _ := hs z.fst
  · change M (lossDefect M z.fst + M z.snd) -
        lossDefect M (M z.fst - lossDefect M z.snd) = z.snd
    simp only [map_add, map_sub, hc]
    calc
      _ = lossDefect M (lossDefect M z.snd) + M (M z.snd) := by abel
      _ = _ := hs z.snd

theorem lossRotation_symmetric (M : H →L[ℂ] H) (hM : 0 ≤ M) (z w : Doubled H) :
    inner ℂ (lossRotationLinear M z) w = inner ℂ z (lossRotationLinear M w) := by
  have hE : (lossDefect M).adjoint = lossDefect M :=
    (IsSelfAdjoint.of_nonneg (lossDefect_nonneg M)).star_eq
  have hMs : M.adjoint = M := (IsSelfAdjoint.of_nonneg hM).star_eq
  change inner ℂ (lossDefect M z.fst + M z.snd) w.fst +
      inner ℂ (M z.fst - lossDefect M z.snd) w.snd =
    inner ℂ z.fst (lossDefect M w.fst + M w.snd) +
      inner ℂ z.snd (M w.fst - lossDefect M w.snd)
  simp only [inner_add_left, inner_sub_left, inner_add_right, inner_sub_right,
    ← ContinuousLinearMap.adjoint_inner_right, hE, hMs]
  abel

theorem lossRotation_inner (M : H →L[ℂ] H) (hM : 0 ≤ M) (hcontract : ‖M‖ ≤ 1)
    (z w : Doubled H) :
    inner ℂ (lossRotationLinear M z) (lossRotationLinear M w) = inner ℂ z w := by
  rw [lossRotation_symmetric M hM, lossRotation_involutive M hM hcontract w]

def lossRotation (M : H →L[ℂ] H) (hM : 0 ≤ M) (hcontract : ‖M‖ ≤ 1) :
    Doubled H ≃ₗᵢ[ℂ] Doubled H where
  toLinearEquiv :=
    { toLinearMap := lossRotationLinear M
      invFun := lossRotationLinear M
      left_inv := lossRotation_involutive M hM hcontract
      right_inv := lossRotation_involutive M hM hcontract }
  norm_map' :=
    (LinearMap.norm_map_iff_inner_map_map (lossRotationLinear M)).mpr
      (lossRotation_inner M hM hcontract)

theorem lossRotation_first_axis (M : H →L[ℂ] H) (hM : 0 ≤ M) (hcontract : ‖M‖ ≤ 1)
    (x : H) :
    lossRotation M hM hcontract (WithLp.toLp 2 (x, (0 : H))) =
      lossEmbedding M hM hcontract x := by
  apply WithLp.ofLp_injective 2
  change (lossDefect M x + M 0, M x - lossDefect M 0) = (lossDefect M x, M x)
  simp

end VortexGap
