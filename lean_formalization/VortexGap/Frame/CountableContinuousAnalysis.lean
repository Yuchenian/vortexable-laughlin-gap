import VortexGap.Frame.CountableContinuousLift
import VortexGap.Frame.LocalBessel
import VortexGap.Fermion.CountableWedgeLinear

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory Filter
open scoped InnerProduct ENNReal Topology

local instance annihilationOperatorNormed (N : ℕ) :
    NormedAddCommGroup (countableSector N →L[ℂ] CountableSpace) :=
  ContinuousLinearMap.toNormedAddCommGroup

attribute [local instance] sectorOperatorNormed

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)
  (p : α → CountablePairSpace)

theorem countablePairAnnihilationField_memLp (hp : MemLp p 2 μ) (N : ℕ) :
    MemLp (fun a => countablePairAnnihilate N (p a)) 2 μ := by
  apply hp.of_le_mul (E := countableSector N →L[ℂ] CountableSpace)
    (f := fun a => countablePairAnnihilate N (p a)) (c := Real.sqrt (N.choose 2 : ℝ))
    (by simpa only [Function.comp_def, countablePairAnnihilateWave_apply] using
      (countablePairAnnihilateWave N).continuous.comp_aestronglyMeasurable hp.aestronglyMeasurable)
  exact Eventually.of_forall fun a => countablePairAnnihilate_opNorm_le N (p a)

theorem countableLocalFrame_energy (hp : MemLp p 2 μ) (N : ℕ) (x : countableSector N) :
    (inner ℂ x (countablePairLift N
      (∫ a, InnerProductSpace.rankOne ℂ (p a) (p a) ∂μ) x)).re =
      ∫ a, ‖countablePairAnnihilate N (p a) x‖^2 ∂μ := by
  have hg := Frame.operatorAnalysis_gram (E := countableSector N) (F := CountableSpace)
    μ (fun a => countablePairAnnihilate N (p a)) (countablePairAnnihilationField_memLp μ p hp N)
  have he := congrArg (fun T : countableSector N →L[ℂ] countableSector N =>
    (inner ℂ x (T x)).re) hg
  rw [countablePairLift_integral μ p hp N]
  refine he.symm.trans ?_
  change (inner ℂ x ((Frame.operatorAnalysis μ _ (countablePairAnnihilationField_memLp μ p hp N)).adjoint
    (Frame.operatorAnalysis μ _ (countablePairAnnihilationField_memLp μ p hp N) x))).re = _
  rw [ContinuousLinearMap.adjoint_inner_right, ← RCLike.re_eq_complex_re,
    ← norm_sq_eq_re_inner (𝕜 := ℂ)]
  exact Frame.operatorAnalysis_norm_sq μ _ (countablePairAnnihilationField_memLp μ p hp N) x

variable (hp : ∀ q, MemLp (fun a => inner ℂ (p a) q) 2 μ)
  (β : ℝ) (hβ : 0 ≤ β)
  (hb : ∀ q, (∫ a, ‖inner ℂ (p a) q‖^2 ∂μ) ≤ β * ‖q‖^2)

include hp hβ hb in
theorem countableLocalFrame_bound (s : Set α) (hs : MeasurableSet s)
    (hloc : MemLp p 2 (μ.restrict s)) (N : ℕ) (x : countableSector N) :
    (∫ a in s, ‖countablePairAnnihilate N (p a) x‖^2 ∂μ) ≤
      ((N.choose 2 : ℝ) * β) * ‖x‖^2 := by
  rw [← countableLocalFrame_energy (μ.restrict s) p hloc N x,
    ← countableContinuousPairCutoff_integral μ p hp β hβ hb s hs hloc]
  let H := countablePairLift N (countableContinuousPairCutoff μ p hp β hβ hb s hs)
  have hn : ‖H‖ ≤ (N.choose 2 : ℝ) * β :=
    (countablePairLift_opNorm_le N _).trans
      (mul_le_mul_of_nonneg_left
        (countableContinuousPairCutoff_norm_le μ p hp β hβ hb s hs) (Nat.cast_nonneg _))
  calc
    _ ≤ ‖x‖ * ‖H x‖ := re_inner_le_norm (𝕜 := ℂ) x (H x)
    _ ≤ ‖x‖ * (((N.choose 2 : ℝ) * β) * ‖x‖) :=
      mul_le_mul_of_nonneg_left (H.le_of_opNorm_le hn x) (norm_nonneg x)
    _ = _ := by ring

variable (s : ℕ → Set α) (hc : AECover μ atTop s)
  (hloc : ∀ n, MemLp p 2 (μ.restrict (s n)))

include hp hβ hb hc hloc in
/-- The global actual annihilation field is L2 on every finite-N vector,
even when the full label measure and the operator-norm envelope are infinite. -/
theorem countableFrameApply_memLp (N : ℕ) (x : countableSector N) :
    MemLp (fun a => countablePairAnnihilate N (p a) x) 2 μ :=
  Frame.localL2_memLp μ s hc _ (fun n => Frame.operatorApply_memLp
    (μ.restrict (s n)) _ (countablePairAnnihilationField_memLp _ p (hloc n) N) x)
    (((N.choose 2 : ℝ) * β) * ‖x‖^2)
    (fun n => countableLocalFrame_bound μ p hp β hβ hb (s n) (hc.measurableSet n) (hloc n) N x)

include hp hβ hb hc hloc in
theorem countableFrameApply_bessel (N : ℕ) (x : countableSector N) :
    (∫ a, ‖countablePairAnnihilate N (p a) x‖^2 ∂μ) ≤
      ((N.choose 2 : ℝ) * β) * ‖x‖^2 :=
  Frame.localL2_integral_le μ s hc _ (fun n => Frame.operatorApply_memLp
    (μ.restrict (s n)) _ (countablePairAnnihilationField_memLp _ p (hloc n) N) x)
    (((N.choose 2 : ℝ) * β) * ‖x‖^2)
    (fun n => countableLocalFrame_bound μ p hp β hβ hb (s n) (hc.measurableSet n) (hloc n) N x)

/-- Actual global many-body analysis, obtained from the local CAR energy identities. -/
def countableContinuousFrameAnalysis (N : ℕ) : countableSector N →L[ℂ] Lp CountableSpace 2 μ :=
  Frame.besselAnalysis μ (fun a => countablePairAnnihilate N (p a))
    (countableFrameApply_memLp μ p hp β hβ hb s hc hloc N)
    ((N.choose 2 : ℝ) * β) (mul_nonneg (Nat.cast_nonneg _) hβ)
    (countableFrameApply_bessel μ p hp β hβ hb s hc hloc N)

theorem countableContinuousFrameAnalysis_ae (N : ℕ) (x : countableSector N) :
    countableContinuousFrameAnalysis μ p hp β hβ hb s hc hloc N x =ᵐ[μ]
      fun a => countablePairAnnihilate N (p a) x :=
  Frame.besselAnalysis_ae μ _ _ _ _ _ x

end VortexGap.Fermion

