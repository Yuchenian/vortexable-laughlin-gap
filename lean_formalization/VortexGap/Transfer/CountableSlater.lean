import VortexGap.Frame.CountableSlaterNoise
import VortexGap.Fermion.CountableSlaterCAR
import VortexGap.Transfer.CountableContinuousFrame
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory Filter VortexGap.Frame
open scoped InnerProduct ENNReal Topology ComplexOrder
variable {α I : Type*} [Fintype I] [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ]
  (p : α → CountablePairSpace)
  (hp : ∀ q, MemLp (fun a => inner ℂ (p a) q) 2 μ)
  (β : ℝ) (hβ : 0 ≤ β)
  (hb : ∀ q, (∫ a, ‖inner ℂ (p a) q‖^2 ∂μ) ≤ β * ‖q‖^2)
  (M : CountableOrbital →L[ℂ] CountableOrbital) (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1)
  (c : α → I → ℂ) (U : α → I → CountableTwoFrame)
  (hpw : ∀ a, p a = countableSlaterPair (c a) (U a))
    (hl : ∀ n i, MemLp (fun a => c a i) 2 (μ.restrict (spanningSets μ n)))
    (hu : ∀ i (l : Fin 2), AEStronglyMeasurable (fun a => U a i (PiLp.single 2 l 1)) μ)
    (ω : α → ℝ) (hω : ∀ a, 0 < ω a) (hωm : AEStronglyMeasurable ω μ)
    (C : ℝ) (hC : 0 ≤ C)
    (hrowInt : ∀ᵐ a ∂μ, Integrable (fun b => countableSlaterKernel (c a) (c b) (U a) (U b) * ω b) μ)
    (hrow : ∀ᵐ a ∂μ, (∫ b, countableSlaterKernel (c a) (c b) (U a) (U b) * ω b ∂μ) ≤ C * ω a)


private abbrev cover := increasingCutoffs_aecover μ (spanningSets μ)
  (measurableSet_spanningSets μ) (monotone_spanningSets μ) (iUnion_spanningSets μ)

include hpw hl hu in
private theorem localPair (n : ℕ) : MemLp p 2 (μ.restrict (spanningSets μ n)) := by
  have he : p = fun a => countableSlaterPair (c a) (U a) := funext hpw
  rw [he]
  exact countableSlaterPair_memLp _ c U (hl n) (fun i l => (hu i l).restrict)

private abbrev filtered := countableContinuousFilteredAnalysis μ p hp β hβ hb (spanningSets μ)
  (cover μ) (localPair μ p c U hpw hl hu) M hM hc
private abbrev synthesis := countableSlaterLossSynthesis μ M c U hc hl hu ω hω hωm C hC hrowInt hrow

def countableSlaterNoiseOne (N : ℕ) : countableSector N →L[ℂ] CountableSpace :=
  (synthesis μ M hc c U hl hu ω hω hωm C hC hrowInt hrow).comp
    (filtered μ p hp β hβ hb M hM hc c U hpw hl hu N)

private abbrev noise := countableSlaterNoiseOne μ p hp β hβ hb M hM hc c U hpw hl hu ω hω hωm C hC hrowInt hrow

theorem countableSlaterNoiseOne_relative (N : ℕ) (x : countableSector N) :
    ‖noise μ p hp β hβ hb M hM hc c U hpw hl hu ω hω hωm C hC hrowInt hrow N x‖^2 ≤
    C*‖1-M^2‖*(inner ℂ x (countableContinuousFilteredHamiltonian μ p hp β hβ hb M hM N x)).re := by
  have hh := countableSlaterLossSynthesis_norm_sq μ M c U hc hl hu ω hω hωm C hC hrowInt hrow hM
    (filtered μ p hp β hβ hb M hM hc c U hpw hl hu N x)
  unfold filtered at hh
  rw [countableContinuousFilteredAnalysis_norm_sq μ p hp β hβ hb (spanningSets μ) (cover μ)
    (localPair μ p c U hpw hl hu) M hM hc (monotone_spanningSets μ) (iUnion_spanningSets μ)] at hh
  exact hh

include hpw in
/-- Actual global vacuum output obtained from the pointwise CAR identity and justified strong limits. -/
theorem countableSlaterLoss_output (N : ℕ) (x : countableSector (N+2)) :
    (countableContinuousDilatedHamiltonian μ p hp β hβ hb M hM hc (N+2)
      (countableFockSector countableSysOrbital (N+2) x) : CountableSpace) =
    countableFockIsometry countableSysOrbital
      (countableContinuousFilteredHamiltonian μ p hp β hβ hb M hM (N+2) x) +
    noise μ p hp β hβ hb M hM hc c U hpw hl hu ω hω hωm C hC hrowInt hrow (N+2) x +
    countableContinuousNoiseTwo μ p hp β hβ hb (spanningSets μ) (cover μ) (localPair μ p c U hpw hl hu) M hM hc (N+2) x := by
  let F := countablePairFilter M hM
  let J := countableLossEmbedding M hM hc
  let P := countablePairMap J
  let V : countableSector (N+2) →L[ℂ] CountableSpace :=
    (countableFockIsometry countableSysOrbital).toContinuousLinearMap.comp
      (countableSector (N+2)).subtypeL
  let xs := countableFockSector countableSysOrbital (N+2) x
  let fL := fun a => (countablePairLift (N+2)
    (InnerProductSpace.rankOne ℂ (P (p a)) (P (p a))) xs : CountableSpace)
  let f0 := fun a => V (countablePairLift (N+2)
    (InnerProductSpace.rankOne ℂ (F (p a)) (F (p a))) x)
  let f1 := fun a => countableSlaterLossColumn M (c a) (U a)
    (countablePairAnnihilate (N+2) (F (p a)) x)
  let f2 := fun a => countablePairLossOutput M
    (countablePairTensor (p a) (countablePairAnnihilate (N+2) (F (p a)) x))
  have hF : ‖F‖ ≤ 1 := countablePairFilter_contract M hM hc
  have hP : ‖P‖ ≤ 1 := (countablePairIsometry J).norm_toContinuousLinearMap_le
  have hL := countableFilteredPairLift_output_integral_tendsto μ p hp β hβ hb
    (spanningSets μ) (cover μ) (localPair μ p c U hpw hl hu) (monotone_spanningSets μ) (iUnion_spanningSets μ)
    P hP (N+2) xs (countableSector (N+2)).subtypeL
  have h0 := countableFilteredPairLift_output_integral_tendsto μ p hp β hβ hb
    (spanningSets μ) (cover μ) (localPair μ p c U hpw hl hu) (monotone_spanningSets μ) (iUnion_spanningSets μ)
    F hF (N+2) x V
  let z := filtered μ p hp β hβ hb M hM hc c U hpw hl hu (N+2) x
  have hae := countableContinuousFilteredAnalysis_ae μ p hp β hβ hb (spanningSets μ) (cover μ)
    (localPair μ p c U hpw hl hu) M hM hc (N+2) x
  have heq (n : ℕ) : (fun a => countableSlaterLossColumn M (c a) (U a) (z a)) =ᵐ[μ.restrict (spanningSets μ n)] f1 := by
    filter_upwards [ae_restrict_of_ae hae] with a ha
    change z a = _ at ha
    simp only [f1,ha,F]
  have h1 := (countableSlaterLossSynthesis_limit μ M c U hc hl hu ω hω hωm C hC hrowInt hrow z).congr'
    (Eventually.of_forall fun n => integral_congr_ae (heq n))
  have h2 := countableContinuousNoiseTwo_integral_tendsto μ p hp β hβ hb
    (spanningSets μ) (cover μ) (localPair μ p c U hpw hl hu) M hM hc (monotone_spanningSets μ) (iUnion_spanningSets μ) (N+2) x
  have he (a : α) : fL a = f0 a + f1 a + f2 a := by
    simpa only [fL,f0,f1,f2,F,P,J,xs,V,ContinuousLinearMap.comp_apply,LinearIsometry.coe_toContinuousLinearMap,
      Submodule.subtypeL_apply,hpw,countableSlaterLossColumn] using countableSlater_rankOne_output M hM hc (c a) (U a) x
  have hi0 (n : ℕ) : Integrable f0 (μ.restrict (spanningSets μ n)) :=
    V.integrable_comp (countablePairLift_rankOne_apply_integrable
      (μ.restrict (spanningSets μ n)) (fun a => F (p a))
      (countableFilteredPair_local_memLp μ p F (spanningSets μ n) (localPair μ p c U hpw hl hu n)) (N+2) x)
  have hi1 (n : ℕ) : Integrable f1 (μ.restrict (spanningSets μ n)) :=
    (countableSlaterLossColumn_local_integrable μ M c U hl hu n z).congr (heq n)
  have hi2 (n : ℕ) : Integrable f2 (μ.restrict (spanningSets μ n)) :=
    countableContinuousNoiseTwo_local_integrable μ p hp β hβ hb (spanningSets μ) (cover μ) (localPair μ p c U hpw hl hu)
      M hM hc (N+2) x n
  have hei (n : ℕ) : (∫ a in spanningSets μ n, fL a ∂μ) =
      (∫ a in spanningSets μ n, f0 a ∂μ) + (∫ a in spanningSets μ n, f1 a ∂μ) +
        (∫ a in spanningSets μ n, f2 a ∂μ) := by
    simp only [he]
    have ha := integral_add ((hi0 n).add (hi1 n)) (hi2 n)
    have hb' := integral_add (hi0 n) (hi1 n)
    simp only [Pi.add_apply] at ha hb'
    exact ha.trans (congrArg (fun z => z + ∫ a in spanningSets μ n, f2 a ∂μ) hb')
  have hr := (h0.add h1).add h2
  change Tendsto (fun n => ∫ a in spanningSets μ n, fL a ∂μ) atTop
    (𝓝 ((countableContinuousDilatedHamiltonian μ p hp β hβ hb M hM hc (N+2) xs : CountableSpace))) at hL
  change Tendsto (fun n => (∫ a in spanningSets μ n, f0 a ∂μ) +
    (∫ a in spanningSets μ n, f1 a ∂μ) + (∫ a in spanningSets μ n, f2 a ∂μ)) atTop
    (𝓝 (countableFockIsometry countableSysOrbital
      (countableContinuousFilteredHamiltonian μ p hp β hβ hb M hM (N+2) x) +
      noise μ p hp β hβ hb M hM hc c U hpw hl hu ω hω hωm C hC hrowInt hrow (N+2) x +
      countableContinuousNoiseTwo μ p hp β hβ hb (spanningSets μ) (cover μ) (localPair μ p c U hpw hl hu) M hM hc (N+2) x)) at hr
  have hr' := hr.congr' (Eventually.of_forall fun n => (hei n).symm)
  exact tendsto_nhds_unique hL hr'

include hpw in
theorem countableSlaterLoss_output_norm_sq (N : ℕ) (x : countableSector (N+2)) :
    ‖countableContinuousDilatedHamiltonian μ p hp β hβ hb M hM hc (N+2)
      (countableFockSector countableSysOrbital (N+2) x)‖^2 =
    ‖countableContinuousFilteredHamiltonian μ p hp β hβ hb M hM (N+2) x‖^2 +
    ‖noise μ p hp β hβ hb M hM hc c U hpw hl hu ω hω hωm C hC hrowInt hrow (N+2) x‖^2 +
    ‖countableContinuousNoiseTwo μ p hp β hβ hb (spanningSets μ) (cover μ) (localPair μ p c U hpw hl hu) M hM hc (N+2) x‖^2 := by
  change ‖(countableContinuousDilatedHamiltonian μ p hp β hβ hb M hM hc (N+2)
    (countableFockSector countableSysOrbital (N+2) x) : CountableSpace)‖^2 = _
  rw [countableSlaterLoss_output μ p hp β hβ hb M hM hc c U hpw hl hu
    ω hω hωm C hC hrowInt hrow N x]
  simp only [noise,countableSlaterNoiseOne, synthesis, countableContinuousNoiseTwo,
    countableSlaterLossSynthesis, countableContinuousTwoSynthesis, countablePairLossOutput,
    ContinuousLinearMap.comp_apply]
  exact countableEnvironmentOutputs_norm_sq _ _ _ _

include hpw hl hu hω hωm hC hrowInt hrow in
theorem countableSlaterLoss_firstMoment (N : ℕ) (x y : countableSector (N+2)) :
    inner ℂ (countableFockSector countableSysOrbital (N+2) x)
      (countableContinuousDilatedHamiltonian μ p hp β hβ hb M hM hc (N+2)
        (countableFockSector countableSysOrbital (N+2) y)) =
      inner ℂ x (countableContinuousFilteredHamiltonian μ p hp β hβ hb M hM (N+2) y) := by
  change inner ℂ (countableFockIsometry countableSysOrbital (x : CountableSpace))
    (countableContinuousDilatedHamiltonian μ p hp β hβ hb M hM hc (N+2)
      (countableFockSector countableSysOrbital (N+2) y) : CountableSpace) =
    inner ℂ (x : CountableSpace)
      (countableContinuousFilteredHamiltonian μ p hp β hβ hb M hM (N+2) y : CountableSpace)
  rw [countableSlaterLoss_output μ p hp β hβ hb M hM hc c U hpw hl hu
    ω hω hωm C hC hrowInt hrow N y]
  simp only [noise,countableSlaterNoiseOne, synthesis, countableContinuousNoiseTwo,
    countableSlaterLossSynthesis, countableContinuousTwoSynthesis, countablePairLossOutput,
    ContinuousLinearMap.comp_apply]
  exact countableEnvironmentOutputs_inner _ _ _ _ _


include hc hl hu hpw hω hωm hC hrowInt hrow in
/-- Concrete continuous-frame transfer; the enlarged reference gap and both noises are derived. -/
theorem countableSlater_transfer_norm_add_two (γ : ℝ) (N : ℕ)
    (hgap : ∀ k ≤ N+2,
      (countablePairLift k (countableContinuousPairOperator μ p hp β hβ hb) *
        countablePairLift k (countableContinuousPairOperator μ p hp β hβ hb) -
        (γ : ℂ) • countablePairLift k (countableContinuousPairOperator μ p hp β hβ hb)).IsPositive)
    (x : countableSector (N+2)) :
    (γ-C*‖1-M^2‖-β*‖1-M^2‖^2) *
      (inner ℂ x (countableContinuousFilteredHamiltonian μ p hp β hβ hb M hM (N+2) x)).re ≤
      ‖countableContinuousFilteredHamiltonian μ p hp β hβ hb M hM (N+2) x‖^2 := by
  let H := countableContinuousFilteredHamiltonian μ p hp β hβ hb M hM (N+2)
  let T := countableContinuousDilatedHamiltonian μ p hp β hβ hb M hM hc (N+2)
  let V := countableFockSector countableSysOrbital (N+2)
  have hg := (quadratic_positive_norm_iff T
    (countableContinuousDilatedHamiltonian_positive μ p hp β hβ hb M hM hc (N+2)) γ).mp
    (countableLoss_pairLift_gap M hM hc (N+2)
      (countableContinuousPairOperator μ p hp β hβ hb) γ hgap) (V x)
  have hf := countableSlaterLoss_firstMoment μ p hp β hβ hb M hM hc c U hpw hl hu ω hω hωm C hC hrowInt hrow N x x
  have hn := countableSlaterLoss_output_norm_sq μ p hp β hβ hb M hM hc c U hpw hl hu ω hω hωm C hC hrowInt hrow N x
  rw [hf, hn] at hg
  have h1 := countableSlaterNoiseOne_relative μ p hp β hβ hb M hM hc c U hpw hl hu ω hω hωm C hC hrowInt hrow (N+2) x
  have h2 := countableContinuousNoiseTwo_relative μ p hp β hβ hb (spanningSets μ) (cover μ) (localPair μ p c U hpw hl hu)
    M hM hc (monotone_spanningSets μ) (iUnion_spanningSets μ) (N+2) x
  change ‖countableSlaterNoiseOne μ p hp β hβ hb M hM hc c U hpw hl hu ω hω hωm C hC hrowInt hrow (N+2) x‖^2 ≤
    C*‖1-M^2‖*(inner ℂ x (H x)).re at h1
  change ‖countableContinuousNoiseTwo μ p hp β hβ hb (spanningSets μ) (cover μ) (localPair μ p c U hpw hl hu)
    M hM hc (N+2) x‖^2 ≤ β*‖1-M^2‖^2*(inner ℂ x (H x)).re at h2
  change (γ-C*‖1-M^2‖-β*‖1-M^2‖^2)*(inner ℂ x (H x)).re ≤ ‖H x‖^2
  nlinarith only [hg,h1,h2]

include hc hl hu hpw hω hωm hC hrowInt hrow in
theorem countableSlater_transfer_norm (γ : ℝ) (N : ℕ)
    (hgap : ∀ k ≤ N,
      (countablePairLift k (countableContinuousPairOperator μ p hp β hβ hb) *
        countablePairLift k (countableContinuousPairOperator μ p hp β hβ hb) -
        (γ : ℂ) • countablePairLift k (countableContinuousPairOperator μ p hp β hβ hb)).IsPositive)
    (x : countableSector N) :
    (γ-C*‖1-M^2‖-β*‖1-M^2‖^2) *
      (inner ℂ x (countableContinuousFilteredHamiltonian μ p hp β hβ hb M hM N x)).re ≤
      ‖countableContinuousFilteredHamiltonian μ p hp β hβ hb M hM N x‖^2 := by
  rcases N with _ | N
  · simp [countableContinuousFilteredHamiltonian, countablePairLift_zero_sector]
  rcases N with _ | N
  · simp [countableContinuousFilteredHamiltonian, countablePairLift_one_sector]
  exact countableSlater_transfer_norm_add_two μ p hp β hβ hb M hM hc c U hpw hl hu ω hω hωm C hC hrowInt hrow γ N hgap x

include hc hl hu hpw hω hωm hC hrowInt hrow in
/-- All-vector operator inequality on each complete fixed-N Hilbert space. -/
theorem countableSlater_transfer (γ : ℝ) (N : ℕ)
    (hgap : ∀ k ≤ N,
      (countablePairLift k (countableContinuousPairOperator μ p hp β hβ hb) *
        countablePairLift k (countableContinuousPairOperator μ p hp β hβ hb) -
        (γ : ℂ) • countablePairLift k (countableContinuousPairOperator μ p hp β hβ hb)).IsPositive) :
    let H := countableContinuousFilteredHamiltonian μ p hp β hβ hb M hM N
    (H*H - ((γ-C*‖1-M^2‖-β*‖1-M^2‖^2 : ℝ) : ℂ) • H).IsPositive := by
  dsimp only
  apply (quadratic_positive_norm_iff _
    (countableContinuousFilteredHamiltonian_positive μ p hp β hβ hb M hM hc N) _).mpr
  intro x
  exact countableSlater_transfer_norm μ p hp β hβ hb M hM hc c U hpw hl hu ω hω hωm C hC hrowInt hrow γ N hgap x


end VortexGap.Fermion
