import VortexGap.Geometry.PlanePairConjugation
import VortexGap.Physical.PlaneBandSpectrum
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory
open scoped ComplexOrder BoundedContinuousFunction

def planeReflectedScalar (f : ℂ →ᵇ ℂ) : ℂ →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun z => f ((starRingEnd ℂ) z))
    (f.continuous.comp Complex.continuous_conj) ‖f‖ (fun z => f.norm_coe_le_norm ((starRingEnd ℂ) z))

theorem planeReflectedScalar_apply (f : ℂ →ᵇ ℂ) (z : ℂ) :
    planeReflectedScalar f z = f ((starRingEnd ℂ) z) := rfl

theorem planePhysicalScale_conj (ell : ℝ) (a : ℂ) :
    (starRingEnd ℂ) ((Real.sqrt 2*ell : ℝ) • (starRingEnd ℂ) a) =
      (Real.sqrt 2*ell : ℝ) • a := by
  change (starRingEnd ℂ) (((Real.sqrt 2*ell : ℝ) : ℂ)* (starRingEnd ℂ) a) = _
  simp

/-- The manuscript's unreflected weight |f(sqrt(2)*ell*alpha)|^4, with the
holomorphic pair coefficients. Its coercivity is transported below, rather than
silently identifying it with the physical weighted operator. -/
def planeUnreflectedPairOperator (ell : ℝ) (f : ℂ →ᵇ ℂ) : CountablePairSpace →L[ℂ] CountablePairSpace :=
  planeWeightedPairOperator ell (planeReflectedScalar f)

theorem planeUnreflectedPairOperator_energy (ell : ℝ) (f : ℂ →ᵇ ℂ) (q : CountablePairSpace) :
    (inner ℂ q (planeUnreflectedPairOperator ell f q)).re =
      ∫ a, ‖f ((Real.sqrt 2*ell : ℝ) • a)‖^4 *
        ‖inner ℂ (countableTwoFramePair (planeTwoFrame a)) q‖^2 ∂planePairMeasure := by
  simp only [planeUnreflectedPairOperator, planeWeightedPairOperator_energy,
    planeReflectedScalar_apply, planePhysicalScale_conj]

theorem planeWeightedPairOperator_energy_reflect (ell : ℝ) (f : ℂ →ᵇ ℂ) (q : CountablePairSpace) :
    (inner ℂ q (planeWeightedPairOperator ell f q)).re =
      (inner ℂ (star q) (planeUnreflectedPairOperator ell f (star q))).re := by
  rw [planeWeightedPairOperator_energy, planeUnreflectedPairOperator_energy]
  have h := planePairMeasure_integral_conj (fun a => ‖f ((Real.sqrt 2*ell : ℝ) • a)‖^4 *
    ‖inner ℂ (countableTwoFramePair (planeTwoFrame a)) (star q)‖^2)
  simpa only [planePair_coefficient_conj] using h

/-- The manuscript's unreflected coercivity suffices for the actual physical
contact, by coefficient conjugation and reference-Q invariance. -/
theorem planeUnreflectedPairOperator_coercivity (ell : ℝ) (f : ℂ →ᵇ ℂ) (κ : ℝ) (hκ : 0 ≤ κ)
    (hw : (κ : ℂ) • planePairOperator ≤ planeUnreflectedPairOperator ell f) :
    (κ : ℂ) • planePairOperator ≤ planeWeightedPairOperator ell f := by
  have hQ : 0 ≤ planePairOperator := ContinuousLinearMap.nonneg_iff_isPositive.mpr planePairOperator_positive
  apply positive_operator_le_of_energy _ _
    (ContinuousLinearMap.nonneg_iff_isPositive.mp (smul_nonneg
      (show 0 ≤ (κ : ℂ) by exact_mod_cast hκ) hQ)) (planeWeightedPairOperator_positive ell f)
  intro q
  simp only [smul_apply, inner_smul_right, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  rw [planeWeightedPairOperator_energy_reflect, ← planePairOperator_energy_star q]
  exact operator_scaled_le_energy _ _ κ hw (star q)

/-- Same physical criterion with the manuscript's unreflected weighted-pair
convention as input. No reflection-symmetry assumption on f is required. -/
theorem physical_scalar_criterion_unreflected (ell : ℝ) (hell : 0 < ell) (f : ℂ →ᵇ ℂ)
    (hf : Differentiable ℝ f) (g u κ γ : ℝ) (hg : 0 < g) (hgu : g ≤ u) (hκ : 0 < κ)
    (hlo : g • (1 : CountableOrbital →L[ℂ] CountableOrbital) ≤ planeScalarGram ell hell f)
    (hhi : planeScalarGram ell hell f ≤ u • (1 : CountableOrbital →L[ℂ] CountableOrbital))
    (hw : (κ : ℂ) • planePairOperator ≤ planeUnreflectedPairOperator ell f)
    (N : ℕ) (hgap : ∀ k ≤ N,
      (countablePairLift k planePairOperator * countablePairLift k planePairOperator -
        (γ : ℂ) • countablePairLift k planePairOperator).IsPositive) :
    let hG : IsStrictlyPositive (planeScalarGram ell hell f) :=
      gramOperator_strict (planeScalarEmbedding ell hell f) g hg hlo
    ∀ t ∈ spectrum ℝ (planeBandContactOperator ell hell f hG hf N),
      t = 0 ∨ κ/g^2*(γ-14*(1-g/u)-(1-g/u)^2) ≤ t :=
  physical_scalar_criterion ell hell f hf g u κ γ hg hgu hκ hlo hhi
    (planeUnreflectedPairOperator_coercivity ell f κ hκ.le hw) N hgap

end VortexGap.Fermion
