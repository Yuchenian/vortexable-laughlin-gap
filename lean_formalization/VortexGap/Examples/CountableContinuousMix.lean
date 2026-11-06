import VortexGap.Transfer.CountableContinuousRaw
import VortexGap.Examples.CountableMix
import VortexGap.Examples.ContinuousPhase
noncomputable section
set_option autoImplicit false
namespace VortexGap.Examples
open MeasureTheory VortexGap.Fermion VortexGap.Frame
open scoped InnerProduct ENNReal ComplexOrder ComplexConjugate

theorem countableContinuousMode_pair (a : CountablePairIndex) :
    countableTwoFramePair (countableModeFrame a) = lp.single 2 a 1 := by
  rw [countableTwoFramePair, countableModeFrame_first, countableModeFrame_second,
    countableWedge_basis]

theorem countableContinuousMode_memLp (a : CountablePairIndex) (q : CountablePairSpace) :
    MemLp (fun _ : ℝ => inner ℂ (countableTwoFramePair (countableModeFrame a)) q) 2 phaseMeasure :=
  memLp_const _

theorem countableContinuousMode_bessel (a : CountablePairIndex) (q : CountablePairSpace) :
    (∫ _ : ℝ, ‖inner ℂ (countableTwoFramePair (countableModeFrame a)) q‖^2 ∂phaseMeasure) ≤
      1 * ‖q‖^2 := by
  rw [integral_const, phaseMeasure_mass, one_smul, one_mul, countableContinuousMode_pair]
  have h := norm_inner_le_norm (𝕜 := ℂ) (lp.single 2 a 1 : CountablePairSpace) q
  rw [countableModePair_norm, one_mul] at h
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

theorem countableContinuousMode_operator (a : CountablePairIndex) :
    countableContinuousPairOperator phaseMeasure (fun _ : ℝ => countableTwoFramePair (countableModeFrame a))
      (countableContinuousMode_memLp a) 1 (by norm_num) (countableContinuousMode_bessel a) =
      InnerProductSpace.rankOne ℂ (lp.single 2 a 1) (lp.single 2 a 1) := by
  apply ContinuousLinearMap.ext
  intro y
  apply ext_inner_left ℂ
  intro x
  rw [countableContinuousPairOperator_inner, integral_const, phaseMeasure_mass, one_smul,
    countableContinuousMode_pair, InnerProductSpace.rankOne_apply, inner_smul_right]
  simp [RCLike.inner_apply, inner_conj_symm, mul_comm]

theorem countableContinuousMode_hamiltonian (a : CountablePairIndex)
    (M : CountableOrbital →L[ℂ] CountableOrbital) (hM : 0 ≤ M) (N : ℕ) :
    countableContinuousFilteredHamiltonian phaseMeasure
      (fun _ : ℝ => countableTwoFramePair (countableModeFrame a))
      (countableContinuousMode_memLp a) 1 (by norm_num) (countableContinuousMode_bessel a) M hM N =
      countablePairLift N (InnerProductSpace.rankOne ℂ
        (countableWedge (M (orbitalKet a.val.1)) (M (orbitalKet a.val.2)))
        (countableWedge (M (orbitalKet a.val.1)) (M (orbitalKet a.val.2)))) := by
  rw [countableContinuousFilteredHamiltonian, countableContinuousMode_operator,
    InnerProductSpace.rankOne_comp, ContinuousLinearMap.adjoint_adjoint,
    InnerProductSpace.comp_rankOne, ← countableWedge_basis, countablePairFilter_wedge]

/-- Nonatomic continuum-label regression through the raw continuous-frame entrance.
The original reference gap is proved for every sector, not assumed. -/
theorem countableContinuousMode_transfer (a : CountablePairIndex)
    (M : CountableOrbital →L[ℂ] CountableOrbital) (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1) (N : ℕ) :
    let p := countableWedge (M (orbitalKet a.val.1)) (M (orbitalKet a.val.2))
    let H := countablePairLift N (InnerProductSpace.rankOne ℂ p p)
    (H*H - ((1-2*‖1-M^2‖-‖1-M^2‖^2 : ℝ) : ℂ) • H).IsPositive := by
  have h := countable_continuous_frame_transfer phaseMeasure (fun _ : ℝ => countableModeFrame a)
    aestronglyMeasurable_const aestronglyMeasurable_const
    (countableContinuousMode_memLp a) 1 (by norm_num) (countableContinuousMode_bessel a)
    M hM hc (fun _ => 1) (by intro; norm_num) aestronglyMeasurable_const 2
    (Filter.Eventually.of_forall fun _ => by
      simp only [countableTwoFrameOverlap_self, traceNormTwo_id, mul_one]
      exact integrable_const 2)
    (Filter.Eventually.of_forall fun _ => by
      simp [countableTwoFrameOverlap_self, traceNormTwo_id, integral_const, phaseMeasure_mass])
    1 N (by
      intro k hk
      rw [countableContinuousMode_operator]
      exact countableModePairLift_gap a k)
  dsimp only at h ⊢
  rw [countableContinuousMode_hamiltonian] at h
  simpa only [one_mul] using h

/-- The new continuous entry certifies the same nonidentity cross-mode filter,
without using the earlier finite-frame transfer theorem to prove the gap. -/
theorem countableContinuousMix_gap (N : ℕ) :
    (countableMixHamiltonian N * countableMixHamiltonian N -
      (9/10 : ℂ) • countableMixHamiltonian N).IsPositive := by
  have h := countableContinuousMode_transfer ⟨(0,1), by decide⟩ countableMixFilter
    countableMixFilter_nonneg countableMixFilter_contraction N
  change (countableMixHamiltonian N * countableMixHamiltonian N -
    ((1-2*‖1-countableMixFilter^2‖-‖1-countableMixFilter^2‖^2 : ℝ) : ℂ) •
      countableMixHamiltonian N).IsPositive at h
  have hh := (VortexGap.quadratic_positive_norm_iff _ (countableMixHamiltonian_positive N)
    (9/10 : ℝ)).mpr (by
      intro x
      have hn := (VortexGap.quadratic_positive_norm_iff _ (countableMixHamiltonian_positive N) _).mp h x
      rw [countableMixFilter_delta] at hn
      have he := (countableMixHamiltonian_positive N).re_inner_nonneg_right x
      nlinarith only [hn, he])
  norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat] at hh
  exact hh
theorem countableContinuousMix_energy :
    (inner ℂ countableMixTest
      (countableContinuousFilteredHamiltonian phaseMeasure
        (fun _ : ℝ => countableTwoFramePair (countableModeFrame ⟨(0,1), by decide⟩))
        (countableContinuousMode_memLp ⟨(0,1), by decide⟩) 1 (by norm_num)
        (countableContinuousMode_bessel ⟨(0,1), by decide⟩)
        countableMixFilter countableMixFilter_nonneg 2 countableMixTest)).re =
      (2491/2500 : ℝ)^2 := by
  rw [countableContinuousMode_hamiltonian]
  exact countableMix_energy

theorem countableContinuousMix_nonzero :
    countableContinuousFilteredHamiltonian phaseMeasure
      (fun _ : ℝ => countableTwoFramePair (countableModeFrame ⟨(0,1), by decide⟩))
      (countableContinuousMode_memLp ⟨(0,1), by decide⟩) 1 (by norm_num)
      (countableContinuousMode_bessel ⟨(0,1), by decide⟩)
      countableMixFilter countableMixFilter_nonneg 2 ≠ 0 := by
  rw [countableContinuousMode_hamiltonian]
  exact countableMixHamiltonian_nonzero
end VortexGap.Examples