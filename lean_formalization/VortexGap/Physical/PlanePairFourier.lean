import VortexGap.Geometry.PlaneFourierMode
import VortexGap.Physical.PlaneWeightConvention
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory
open scoped InnerProduct ComplexConjugate BoundedContinuousFunction

/-- Compression of any bounded position-space symbol to the physical LLL. -/
def planeToeplitz (ell : ℝ) (hell : 0 < ell) (a : ℂ →ᵇ ℂ) :=
  (planeLLLEmbedding ell hell).toContinuousLinearMap.adjoint.comp (planeScalarEmbedding ell hell a)

theorem planeToeplitz_energy (ell : ℝ) (hell : 0 < ell) (a : ℂ →ᵇ ℂ) (v : CountableOrbital) :
    inner ℂ v (planeToeplitz ell hell a v) =
      ∫ z, a z * ((‖inner ℂ (planeEvaluation ell z) v‖^2 : ℝ) : ℂ) := by
  change inner ℂ v ((planeLLLEmbedding ell hell).toContinuousLinearMap.adjoint _) = _
  rw [ContinuousLinearMap.adjoint_inner_right, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [planeLLLEmbedding_coe ell hell v, planeScalarEmbedding_coe ell hell a v] with z hv ha
  change inner ℂ (planeLLLEmbedding ell hell v z) (planeScalarEmbedding ell hell a v z) = _
  rw [hv, ha, RCLike.inner_apply', Complex.sq_norm, ← Complex.mul_conj]
  ring

private theorem center_change (L : ℝ) (hL : 0 < L) (a : ℂ →ᵇ ℂ) (v : CountableOrbital) :
    inner ℂ v (planeToeplitz L hL a v) = ∫ u, a ((2*L : ℝ) • u) *
      ((‖∑' n, v n * planePairAmplitude u (n+1)‖^2 : ℝ) : ℂ) ∂planePairMeasure := by
  let F := fun u : ℂ => a ((2*L : ℝ) • u) * ((‖∑' n, v n * planePairAmplitude u (n+1)‖^2 : ℝ) : ℂ)
  let r := 2*Real.pi*L^2
  have hr : 0 < r := by dsimp [r]; positivity
  have ht : 2*L ≠ 0 := by positivity
  have hrow (z : ℂ) : a z * ((‖inner ℂ (planeEvaluation L z) v‖^2 : ℝ) : ℂ) =
      (r⁻¹ : ℂ) * F ((2*L : ℝ)⁻¹ • z) := by
    simp only [F,smul_smul,mul_inv_cancel₀ ht,one_smul,planeEvaluation_amplitude_series L hL,
      norm_mul,mul_pow,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),
      inv_pow, Real.sq_sqrt (by positivity : 0 ≤ 2*Real.pi*L^2),Complex.ofReal_mul,Complex.ofReal_inv]
    dsimp [r]
    push_cast
    ring
  rw [planeToeplitz_energy]
  simp_rw [hrow]
  rw [integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg volume F (by positivity : 0 ≤ 2*L),
    Complex.finrank_real_complex, planePairMeasure, integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity)]
  change (r : ℂ)⁻¹ * (((2*L : ℝ)^2 : ℝ) • ∫ u, F u) = (2/Real.pi : ℝ) • ∫ u, F u
  simp only [r, Complex.real_smul,Complex.ofReal_pow, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_ofNat]
  have hn : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hl : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL.ne'
  field_simp

/-- Physical reflected pair convention; complex symbols retain their phase. -/
theorem planePair_symbol_center (ell : ℝ) (hell : 0 < ell) (a : ℂ →ᵇ ℂ) (p : CountablePairSpace) :
    (∫ u, a ((Real.sqrt 2*ell : ℝ) • conj u) *
        ((‖inner ℂ (countableTwoFramePair (planeTwoFrame u)) p‖^2 : ℝ) : ℂ) ∂planePairMeasure) =
      inner ℂ (planePairRightCoordinates (star p))
        (planeToeplitz (ell/Real.sqrt 2) (by positivity) a (planePairRightCoordinates (star p))) := by
  rw [center_change]
  have hs : 2*(ell/Real.sqrt 2) = Real.sqrt 2*ell := by
    field_simp
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  rw [hs]
  simp_rw [← planePair_right_coefficient_series, norm_inner_symm (star p)]
  let F := fun u : ℂ => a ((Real.sqrt 2*ell : ℝ) • u) *
    ((‖inner ℂ (countableTwoFramePair (planeTwoFrame u)) (star p)‖^2 : ℝ) : ℂ)
  have hi : (∫ u, F (conj u) ∂planePairMeasure) = ∫ u, F u ∂planePairMeasure := by
    rw [planePairMeasure,integral_smul_measure,integral_smul_measure]
    congr 1
    exact Complex.conjLIE.measurePreserving.integral_comp Complex.conjLIE.toHomeomorph.measurableEmbedding F
  change _ = ∫ u, F u ∂planePairMeasure
  rw [← hi]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun u => by simp only [F,planePair_coefficient_conj]

theorem planePair_fourier_factor (ell : ℝ) (hell : 0 < ell) (q : ℂ) (p : CountablePairSpace) :
    (∫ u, planeFourierPhase q ((Real.sqrt 2*ell : ℝ) • conj u) *
        ((‖inner ℂ (countableTwoFramePair (planeTwoFrame u)) p‖^2 : ℝ) : ℂ) ∂planePairMeasure) =
      ((Real.exp (-‖q‖^2*ell^2/8) : ℝ) : ℂ) * inner ℂ (planePairRightCoordinates (star p))
        (planeGuidingTranslation (ell/Real.sqrt 2) (by positivity) q (planePairRightCoordinates (star p))) := by
  rw [planePair_symbol_center ell hell, planeToeplitz, planeFourier_compression,
    smul_apply,inner_smul_right]
  have he : -‖q‖^2*(ell/Real.sqrt 2)^2/4 = -‖q‖^2*ell^2/8 := by
    rw [div_pow,Real.sq_sqrt (by norm_num)]
    ring
  rw [he]
  rfl

/-- Quadratic form of the actual contact weight in the center-of-mass LLL. -/
theorem planeWeightedPair_center_energy (ell : ℝ) (hell : 0 < ell) (f : ℂ →ᵇ ℂ) (p : CountablePairSpace) :
    (inner ℂ p (planeWeightedPairOperator ell f p)).re =
      (inner ℂ (planePairRightCoordinates (star p))
        (planeToeplitz (ell/Real.sqrt 2) (by positivity) ((star f*f)^2)
          (planePairRightCoordinates (star p)))).re := by
  rw [← planePair_symbol_center ell hell, planeWeightedPairOperator_energy]
  have he (z : ℂ) : ((star f*f)^2) z = ((‖f z‖^4 : ℝ) : ℂ) := by
    change (conj (f z) * f z)^2 = _
    rw [mul_comm, Complex.mul_conj, ← Complex.sq_norm, ← Complex.ofReal_pow]
    ring_nf
  simp_rw [he, ← Complex.ofReal_mul]
  rw [integral_complex_ofReal]
  rfl

end VortexGap.Fermion
