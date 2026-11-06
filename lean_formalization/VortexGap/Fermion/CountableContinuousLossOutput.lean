import VortexGap.Frame.CountableContinuousOneNoise
import VortexGap.Frame.CountableContinuousLiftLimits
import VortexGap.Fermion.CountableEnvironmentRanges

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory Filter VortexGap.Frame
open scoped InnerProduct ENNReal Topology ComplexOrder
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

/-- Concrete filtered fixed-sector CAR lift. -/
def countableContinuousFilteredHamiltonian (N : ℕ) : countableSector N →L[ℂ] countableSector N :=
  countablePairLift N ((countablePairFilter M hM).comp
    ((countableContinuousPairOperator μ p hp β hβ hb).comp (countablePairFilter M hM).adjoint))

/-- Reference Hamiltonian in the actual loss-embedded one-particle subspace. -/
def countableContinuousDilatedHamiltonian (N : ℕ) : countableSector N →L[ℂ] countableSector N :=
  countablePairLift N (countablePairConjugate (countableLossEmbedding M hM hMc)
    (countableContinuousPairOperator μ p hp β hβ hb))

include hpw in
/-- Actual global vacuum output obtained from the pointwise CAR identity and justified strong limits. -/
theorem countableContinuousLoss_output (N : ℕ) (x : countableSector (N+2)) :
    (countableContinuousDilatedHamiltonian μ p hp β hβ hb M hM hMc (N+2)
      (countableFockSector countableSysOrbital (N+2) x) : CountableSpace) =
    countableFockIsometry countableSysOrbital
      (countableContinuousFilteredHamiltonian μ p hp β hβ hb M hM (N+2) x) +
    countableContinuousNoiseOne μ p hp β hβ hb (spanningSets μ) hcov hloc M hM hMc
      U hU0 hU1 ω hω hωm C hC hrowInt hrow (N+2) x +
    countableContinuousNoiseTwo μ p hp β hβ hb (spanningSets μ) hcov hloc M hM hMc (N+2) x := by
  let F := countablePairFilter M hM
  let J := countableLossEmbedding M hM hMc
  let P := countablePairMap J
  let V : countableSector (N+2) →L[ℂ] CountableSpace :=
    (countableFockIsometry countableSysOrbital).toContinuousLinearMap.comp
      (countableSector (N+2)).subtypeL
  let xs := countableFockSector countableSysOrbital (N+2) x
  let fL := fun a => (countablePairLift (N+2)
    (InnerProductSpace.rankOne ℂ (P (p a)) (P (p a))) xs : CountableSpace)
  let f0 := fun a => V (countablePairLift (N+2)
    (InnerProductSpace.rankOne ℂ (F (p a)) (F (p a))) x)
  let f1 := fun a => countableLossCreationOne M (U a (PiLp.single 2 0 1)) (U a (PiLp.single 2 1 1))
    (countablePairAnnihilate (N+2) (F (p a)) x)
  let f2 := fun a => countablePairLossOutput M
    (countablePairTensor (p a) (countablePairAnnihilate (N+2) (F (p a)) x))
  have hF : ‖F‖ ≤ 1 := countablePairFilter_contract M hM hMc
  have hP : ‖P‖ ≤ 1 := (countablePairIsometry J).norm_toContinuousLinearMap_le
  have hL := countableFilteredPairLift_output_integral_tendsto μ p hp β hβ hb
    (spanningSets μ) hcov hloc (monotone_spanningSets μ) (iUnion_spanningSets μ)
    P hP (N+2) xs (countableSector (N+2)).subtypeL
  have h0 := countableFilteredPairLift_output_integral_tendsto μ p hp β hβ hb
    (spanningSets μ) hcov hloc (monotone_spanningSets μ) (iUnion_spanningSets μ)
    F hF (N+2) x V
  have h1 := countableContinuousNoiseOne_integral_tendsto μ p hp β hβ hb
    (spanningSets μ) hcov hloc M hM hMc U hU0 hU1 ω hω hωm C hC hrowInt hrow (N+2) x
  have h2 := countableContinuousNoiseTwo_integral_tendsto μ p hp β hβ hb
    (spanningSets μ) hcov hloc M hM hMc (monotone_spanningSets μ) (iUnion_spanningSets μ) (N+2) x
  have he (a : α) : fL a = f0 a + f1 a + f2 a := by
    have h := countableLoss_rankOne_output M hM hMc
      (U a (PiLp.single 2 0 1)) (U a (PiLp.single 2 1 1)) x
    rw [countablePairConjugate_rankOne] at h
    simpa only [fL, f0, f1, f2, F, P, J, xs, V, ContinuousLinearMap.comp_apply,
      LinearIsometry.coe_toContinuousLinearMap, Submodule.subtypeL_apply,
      hpw, countablePairFilter_wedge, countablePairLossOutput_wedge] using h
  have hi0 (n : ℕ) : Integrable f0 (μ.restrict (spanningSets μ n)) :=
    V.integrable_comp (countablePairLift_rankOne_apply_integrable
      (μ.restrict (spanningSets μ n)) (fun a => F (p a))
      (countableFilteredPair_local_memLp μ p F (spanningSets μ n) (hloc n)) (N+2) x)
  have hi1 (n : ℕ) : Integrable f1 (μ.restrict (spanningSets μ n)) :=
    countableContinuousNoiseOne_local_integrable μ p hp β hβ hb (spanningSets μ) hcov hloc
      M hM hMc U hU0 hU1 (N+2) x n
  have hi2 (n : ℕ) : Integrable f2 (μ.restrict (spanningSets μ n)) :=
    countableContinuousNoiseTwo_local_integrable μ p hp β hβ hb (spanningSets μ) hcov hloc
      M hM hMc (N+2) x n
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
    (𝓝 ((countableContinuousDilatedHamiltonian μ p hp β hβ hb M hM hMc (N+2) xs : CountableSpace))) at hL
  change Tendsto (fun n => (∫ a in spanningSets μ n, f0 a ∂μ) +
    (∫ a in spanningSets μ n, f1 a ∂μ) + (∫ a in spanningSets μ n, f2 a ∂μ)) atTop
    (𝓝 (countableFockIsometry countableSysOrbital
      (countableContinuousFilteredHamiltonian μ p hp β hβ hb M hM (N+2) x) +
      countableContinuousNoiseOne μ p hp β hβ hb (spanningSets μ) hcov hloc M hM hMc
        U hU0 hU1 ω hω hωm C hC hrowInt hrow (N+2) x +
      countableContinuousNoiseTwo μ p hp β hβ hb (spanningSets μ) hcov hloc M hM hMc (N+2) x)) at hr
  have hr' := hr.congr' (Eventually.of_forall fun n => (hei n).symm)
  exact tendsto_nhds_unique hL hr'

include hpw in
theorem countableContinuousLoss_output_norm_sq (N : ℕ) (x : countableSector (N+2)) :
    ‖countableContinuousDilatedHamiltonian μ p hp β hβ hb M hM hMc (N+2)
      (countableFockSector countableSysOrbital (N+2) x)‖^2 =
    ‖countableContinuousFilteredHamiltonian μ p hp β hβ hb M hM (N+2) x‖^2 +
    ‖countableContinuousNoiseOne μ p hp β hβ hb (spanningSets μ) hcov hloc M hM hMc
      U hU0 hU1 ω hω hωm C hC hrowInt hrow (N+2) x‖^2 +
    ‖countableContinuousNoiseTwo μ p hp β hβ hb (spanningSets μ) hcov hloc M hM hMc (N+2) x‖^2 := by
  change ‖(countableContinuousDilatedHamiltonian μ p hp β hβ hb M hM hMc (N+2)
    (countableFockSector countableSysOrbital (N+2) x) : CountableSpace)‖^2 = _
  rw [countableContinuousLoss_output μ p hp β hβ hb hcov hloc M hM hMc U hU0 hU1 hpw
    ω hω hωm C hC hrowInt hrow N x]
  simp only [countableContinuousNoiseOne, countableContinuousNoiseTwo,
    countableContinuousOneLossSynthesis, countableContinuousTwoSynthesis, countablePairLossOutput,
    ContinuousLinearMap.comp_apply]
  exact countableEnvironmentOutputs_norm_sq _ _ _ _

include hpw hcov hloc hU0 hU1 hω hωm hC hrowInt hrow in
theorem countableContinuousLoss_firstMoment (N : ℕ) (x y : countableSector (N+2)) :
    inner ℂ (countableFockSector countableSysOrbital (N+2) x)
      (countableContinuousDilatedHamiltonian μ p hp β hβ hb M hM hMc (N+2)
        (countableFockSector countableSysOrbital (N+2) y)) =
      inner ℂ x (countableContinuousFilteredHamiltonian μ p hp β hβ hb M hM (N+2) y) := by
  change inner ℂ (countableFockIsometry countableSysOrbital (x : CountableSpace))
    (countableContinuousDilatedHamiltonian μ p hp β hβ hb M hM hMc (N+2)
      (countableFockSector countableSysOrbital (N+2) y) : CountableSpace) =
    inner ℂ (x : CountableSpace)
      (countableContinuousFilteredHamiltonian μ p hp β hβ hb M hM (N+2) y : CountableSpace)
  rw [countableContinuousLoss_output μ p hp β hβ hb hcov hloc M hM hMc U hU0 hU1 hpw
    ω hω hωm C hC hrowInt hrow N y]
  simp only [countableContinuousNoiseOne, countableContinuousNoiseTwo,
    countableContinuousOneLossSynthesis, countableContinuousTwoSynthesis, countablePairLossOutput,
    ContinuousLinearMap.comp_apply]
  exact countableEnvironmentOutputs_inner _ _ _ _ _

end VortexGap.Fermion
