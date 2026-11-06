import VortexGap.Fermion.CountableContinuousMoments
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory Filter VortexGap.Frame
open scoped InnerProduct ENNReal ComplexOrder

private lemma gram_bound_of_norm
    {E K : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (H : E →L[ℂ] E) (X : E →L[ℂ] K) (hH : H.IsPositive) (c : ℝ)
    (hn : ∀ x, ‖X x‖^2 ≤ c * (inner ℂ x (H x)).re) :
    ((c : ℂ) • H - X.adjoint.comp X).IsPositive := by
  have hr (x : E) : ((inner ℂ x (H x)).re : ℂ) = inner ℂ x (H x) := by
    have h := (ContinuousLinearMap.isPositive_iff_complex H).mp hH x
    simpa only [hH.inner_left_eq_inner_right, RCLike.re_eq_complex_re] using h.1
  have hi (x : E) : inner ℂ (((c : ℂ) • H - X.adjoint.comp X) x) x =
      ((c * (inner ℂ x (H x)).re - ‖X x‖^2 : ℝ) : ℂ) := by
    simp only [sub_apply, smul_apply, ContinuousLinearMap.comp_apply,
      inner_sub_left, inner_smul_left, Complex.conj_ofReal]
    rw [hH.inner_left_eq_inner_right, ContinuousLinearMap.adjoint_inner_left,
      inner_self_eq_norm_sq_to_K, ← hr x]
    push_cast
    rfl
  rw [ContinuousLinearMap.isPositive_iff_complex]
  intro x
  rw [hi]
  simpa only [RCLike.re_eq_complex_re, Complex.ofReal_re, true_and] using
    (sub_nonneg.mpr (hn x))

private lemma map_zero_of_norm_sq
    {E K : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup K] [NormedSpace ℂ K]
    (X : E →L[ℂ] K) (h : ∀ x, ‖X x‖^2 ≤ 0) : X = 0 := by
  ext x
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm (h x) (sq_nonneg _)))
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

theorem countableContinuousNoiseOne_operator_bound (N : ℕ) :
    let H := countableContinuousFilteredHamiltonian μ p hp β hβ hb M hM N
    let X := countableContinuousNoiseOne μ p hp β hβ hb (spanningSets μ) hcov hloc
      M hM hMc U hU0 hU1 ω hω hωm C hC hrowInt hrow N
    (((C*‖1-M^2‖ : ℝ) : ℂ) • H - X.adjoint.comp X).IsPositive := by
  apply gram_bound_of_norm _ _
    (countableContinuousFilteredHamiltonian_positive μ p hp β hβ hb M hM hMc N)
  intro x
  exact countableContinuousNoiseOne_relative μ p hp β hβ hb (spanningSets μ) hcov hloc
    M hM hMc U hU0 hU1 ω hω hωm C hC hrowInt hrow
    (monotone_spanningSets μ) (iUnion_spanningSets μ) N x

theorem countableContinuousNoiseTwo_operator_bound (N : ℕ) :
    let H := countableContinuousFilteredHamiltonian μ p hp β hβ hb M hM N
    let X := countableContinuousNoiseTwo μ p hp β hβ hb (spanningSets μ) hcov hloc M hM hMc N
    (((β*‖1-M^2‖^2 : ℝ) : ℂ) • H - X.adjoint.comp X).IsPositive := by
  apply gram_bound_of_norm _ _
    (countableContinuousFilteredHamiltonian_positive μ p hp β hβ hb M hM hMc N)
  intro x
  exact countableContinuousNoiseTwo_relative μ p hp β hβ hb (spanningSets μ) hcov hloc
    M hM hMc (monotone_spanningSets μ) (iUnion_spanningSets μ) N x

theorem countableContinuousNoiseOne_low_sector (N : ℕ) (hN : N < 2) :
    countableContinuousNoiseOne μ p hp β hβ hb (spanningSets μ) hcov hloc
      M hM hMc U hU0 hU1 ω hω hωm C hC hrowInt hrow N = 0 := by
  apply map_zero_of_norm_sq
  intro x
  have h := countableContinuousNoiseOne_relative μ p hp β hβ hb (spanningSets μ) hcov hloc
    M hM hMc U hU0 hU1 ω hω hωm C hC hrowInt hrow
    (monotone_spanningSets μ) (iUnion_spanningSets μ) N x
  interval_cases N <;> simpa [countablePairLift_zero_sector, countablePairLift_one_sector] using h

theorem countableContinuousNoiseTwo_low_sector (N : ℕ) (hN : N < 2) :
    countableContinuousNoiseTwo μ p hp β hβ hb (spanningSets μ) hcov hloc M hM hMc N = 0 := by
  apply map_zero_of_norm_sq
  intro x
  have h := countableContinuousNoiseTwo_relative μ p hp β hβ hb (spanningSets μ) hcov hloc
    M hM hMc (monotone_spanningSets μ) (iUnion_spanningSets μ) N x
  interval_cases N <;> simpa [countablePairLift_zero_sector, countablePairLift_one_sector] using h

include hpw in
theorem countableContinuousLoss_secondMoment (N : ℕ) :
    let V := (countableFockSector countableSysOrbital N).toContinuousLinearMap
    let T := countableContinuousDilatedHamiltonian μ p hp β hβ hb M hM hMc N
    let H := countableContinuousFilteredHamiltonian μ p hp β hβ hb M hM N
    let X1 := countableContinuousNoiseOne μ p hp β hβ hb (spanningSets μ) hcov hloc
      M hM hMc U hU0 hU1 ω hω hωm C hC hrowInt hrow N
    let X2 := countableContinuousNoiseTwo μ p hp β hβ hb (spanningSets μ) hcov hloc M hM hMc N
    V.adjoint.comp ((T*T).comp V) = H*H + X1.adjoint.comp X1 + X2.adjoint.comp X2 := by
  by_cases hn : N < 2
  · dsimp only
    rw [countableContinuousNoiseOne_low_sector μ p hp β hβ hb hcov hloc M hM hMc
      U hU0 hU1 ω hω hωm C hC hrowInt hrow N hn,
      countableContinuousNoiseTwo_low_sector μ p hp β hβ hb hcov hloc M hM hMc N hn]
    interval_cases N <;>
      simp [countableContinuousDilatedHamiltonian, countableContinuousFilteredHamiltonian,
        countablePairLift_zero_sector, countablePairLift_one_sector] <;> ext x <;> simp
  · obtain ⟨k, rfl⟩ : ∃ k, N = k+2 := ⟨N-2, by omega⟩
    exact countableContinuousLoss_secondMoment_add_two μ p hp β hβ hb hcov hloc M hM hMc
      U hU0 hU1 hpw ω hω hωm C hC hrowInt hrow k
end VortexGap.Fermion