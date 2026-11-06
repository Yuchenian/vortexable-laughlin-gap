import VortexGap.Transfer.CountableContinuousFrame
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory Filter VortexGap.Frame
open scoped InnerProduct ENNReal ComplexOrder
private lemma secondMoment_of_norm
    {E K : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (V T H : E →L[ℂ] E) (X1 X2 : E →L[ℂ] K)
    (hT : T.IsPositive) (hH : H.IsPositive)
    (hn : ∀ x, ‖T (V x)‖^2 = ‖H x‖^2 + ‖X1 x‖^2 + ‖X2 x‖^2) :
    V.adjoint.comp ((T*T).comp V) = H*H + X1.adjoint.comp X1 + X2.adjoint.comp X2 := by
  have he : (V.adjoint.comp ((T*T).comp V)).toLinearMap =
      (H*H + X1.adjoint.comp X1 + X2.adjoint.comp X2).toLinearMap := by
    apply (ext_inner_map _ _).mp
    intro x
    change inner ℂ (V.adjoint (T (T (V x)))) x =
      inner ℂ (H (H x) + X1.adjoint (X1 x) + X2.adjoint (X2 x)) x
    rw [ContinuousLinearMap.adjoint_inner_left, hT.inner_left_eq_inner_right,
      inner_add_left, inner_add_left, hH.inner_left_eq_inner_right,
      ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left]
    simp only [inner_self_eq_norm_sq_to_K]
    exact_mod_cast hn x
  exact ContinuousLinearMap.coe_injective he

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ]
  (p : α → CountablePairSpace)
  (hp : ∀ q, MemLp (fun a => inner ℂ (p a) q) 2 μ)
  (β : ℝ) (hβ : 0 ≤ β)
  (hb : ∀ q, (∫ a, ‖inner ℂ (p a) q‖^2 ∂μ) ≤ β * ‖q‖^2)
  (hcov : AECover μ atTop (spanningSets μ))
  (hloc : ∀ n, MemLp p 2 (μ.restrict (spanningSets μ n)))
  (M : CountableOrbital →L[ℂ] CountableOrbital) (hM : 0 ≤ M) (hMc : ‖M‖ ≤ 1)
  (U : α → CountableTwoFrame)
  (hU0 : AEStronglyMeasurable (fun a => U a (PiLp.single 2 0 1)) μ)
  (hU1 : AEStronglyMeasurable (fun a => U a (PiLp.single 2 1 1)) μ)
  (hpw : ∀ a, p a = countableWedge (U a (PiLp.single 2 0 1)) (U a (PiLp.single 2 1 1)))
  (ω : α → ℝ) (hω : ∀ a, 0 < ω a) (hωm : AEStronglyMeasurable ω μ)
  (C : ℝ) (hC : 0 ≤ C)
  (hrowInt : ∀ᵐ a ∂μ, Integrable
    (fun b => traceNormTwo (countableTwoFrameOverlap (U a) (U b)) * ω b) μ)
  (hrow : ∀ᵐ a ∂μ,
    (∫ b, traceNormTwo (countableTwoFrameOverlap (U a) (U b)) * ω b ∂μ) ≤ C * ω a)

include hcov hloc hU0 hU1 hpw hω hωm hC hrowInt hrow in
theorem countableContinuousLoss_compression (N : ℕ) :
    let V := (countableFockSector countableSysOrbital N).toContinuousLinearMap
    let T := countableContinuousDilatedHamiltonian μ p hp β hβ hb M hM hMc N
    V.adjoint.comp (T.comp V) =
      countableContinuousFilteredHamiltonian μ p hp β hβ hb M hM N := by
  dsimp only
  rcases N with _ | N
  · simp [countableContinuousDilatedHamiltonian, countableContinuousFilteredHamiltonian,
      countablePairLift_zero_sector]
  rcases N with _ | N
  · simp [countableContinuousDilatedHamiltonian, countableContinuousFilteredHamiltonian,
      countablePairLift_one_sector]
  apply ContinuousLinearMap.ext
  intro y
  apply ext_inner_left ℂ
  intro x
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    LinearIsometry.coe_toContinuousLinearMap]
  exact countableContinuousLoss_firstMoment μ p hp β hβ hb hcov hloc M hM hMc
    U hU0 hU1 hpw ω hω hωm C hC hrowInt hrow N x y

include hpw in
theorem countableContinuousLoss_secondMoment_add_two (N : ℕ) :
    let V := (countableFockSector countableSysOrbital (N+2)).toContinuousLinearMap
    let T := countableContinuousDilatedHamiltonian μ p hp β hβ hb M hM hMc (N+2)
    let H := countableContinuousFilteredHamiltonian μ p hp β hβ hb M hM (N+2)
    let X1 := countableContinuousNoiseOne μ p hp β hβ hb (spanningSets μ) hcov hloc
      M hM hMc U hU0 hU1 ω hω hωm C hC hrowInt hrow (N+2)
    let X2 := countableContinuousNoiseTwo μ p hp β hβ hb (spanningSets μ) hcov hloc
      M hM hMc (N+2)
    V.adjoint.comp ((T*T).comp V) = H*H + X1.adjoint.comp X1 + X2.adjoint.comp X2 := by
  dsimp only
  let V := (countableFockSector countableSysOrbital (N+2)).toContinuousLinearMap
  let T := countableContinuousDilatedHamiltonian μ p hp β hβ hb M hM hMc (N+2)
  let H := countableContinuousFilteredHamiltonian μ p hp β hβ hb M hM (N+2)
  let X1 := countableContinuousNoiseOne μ p hp β hβ hb (spanningSets μ) hcov hloc
    M hM hMc U hU0 hU1 ω hω hωm C hC hrowInt hrow (N+2)
  let X2 := countableContinuousNoiseTwo μ p hp β hβ hb (spanningSets μ) hcov hloc
    M hM hMc (N+2)
  change V.adjoint.comp ((T*T).comp V) = H*H + X1.adjoint.comp X1 + X2.adjoint.comp X2
  have hT : T.IsPositive := countableContinuousDilatedHamiltonian_positive μ p hp β hβ hb M hM hMc (N+2)
  have hH : H.IsPositive := countableContinuousFilteredHamiltonian_positive μ p hp β hβ hb M hM hMc (N+2)
  apply secondMoment_of_norm V T H X1 X2 hT hH
  intro x
  exact countableContinuousLoss_output_norm_sq μ p hp β hβ hb hcov hloc M hM hMc
    U hU0 hU1 hpw ω hω hωm C hC hrowInt hrow N x
end VortexGap.Fermion