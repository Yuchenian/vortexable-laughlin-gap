import VortexGap.Physical.PlaneBandSpectrum
import VortexGap.Physical.PlaneGramBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped ComplexOrder BoundedContinuousFunction

def planeWeakCosValue (z : ℂ) : ℝ := 1+Real.cos z.re/10000

theorem planeWeakCosValue_bounds (z : ℂ) :
    (9999/10000 : ℝ) ≤ planeWeakCosValue z ∧ planeWeakCosValue z ≤ (10001/10000 : ℝ) := by
  dsimp [planeWeakCosValue]
  constructor <;> nlinarith [Real.neg_one_le_cos z.re, Real.cos_le_one z.re]

def planeWeakCos : ℂ →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun z => (planeWeakCosValue z : ℂ))
    (by unfold planeWeakCosValue; fun_prop) 2 (fun z => by
      rw [Complex.norm_real, Real.norm_eq_abs]
      have h := planeWeakCosValue_bounds z
      rw [abs_of_nonneg (by linarith : 0 ≤ planeWeakCosValue z)]
      linarith)

theorem planeWeakCos_norm (z : ℂ) : ‖planeWeakCos z‖ = planeWeakCosValue z := by
  change ‖(planeWeakCosValue z : ℂ)‖ = _
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
  linarith [(planeWeakCosValue_bounds z).1]

theorem planeWeakCos_differentiable : Differentiable ℝ planeWeakCos := by
  change Differentiable ℝ (fun z : ℂ => ((1+Real.cos z.re/10000 : ℝ) : ℂ))
  fun_prop

theorem planeWeakCos_nonconstant : planeWeakCos 0 ≠ planeWeakCos (Real.pi : ℂ) := by
  change ((planeWeakCosValue 0 : ℝ) : ℂ) ≠ (planeWeakCosValue (Real.pi : ℂ) : ℂ)
  norm_num [planeWeakCosValue]

theorem planeWeakCos_gram_bounds (ell : ℝ) (hell : 0 < ell) :
    ((9999/10000 : ℝ)^2) • (1 : CountableOrbital →L[ℂ] CountableOrbital) ≤ planeScalarGram ell hell planeWeakCos ∧
      planeScalarGram ell hell planeWeakCos ≤ ((10001/10000 : ℝ)^2) • (1 : CountableOrbital →L[ℂ] CountableOrbital) := by
  apply planeScalarGram_pointwise_bounds ell hell planeWeakCos _ _ (by positivity) (by positivity)
  intro z
  rw [planeWeakCos_norm]
  have h := planeWeakCosValue_bounds z
  exact ⟨pow_le_pow_left₀ (by norm_num) h.1 2,
    pow_le_pow_left₀ (by linarith : 0 ≤ planeWeakCosValue z) h.2 2⟩

theorem planeWeakCos_coercivity (ell : ℝ) :
    (((9999/10000 : ℝ)^4 : ℝ) : ℂ) • planePairOperator ≤ planeWeightedPairOperator ell planeWeakCos := by
  apply planeWeightedPairOperator_lower ell planeWeakCos _ (by positivity)
  intro z
  rw [planeWeakCos_norm]
  exact pow_le_pow_left₀ (by norm_num) (planeWeakCosValue_bounds z).1 4

def planeWeakCosContactOperator (ell : ℝ) (hell : 0 < ell) (N : ℕ) :
    countableSector N →L[ℂ] countableSector N :=
  planeBandContactOperator ell hell planeWeakCos
    (gramOperator_strict _ ((9999/10000 : ℝ)^2) (by norm_num) (planeWeakCos_gram_bounds ell hell).1)
    planeWeakCos_differentiable N

/-- Nonconstant physical instance, conditional on the explicitly supplied old
reference gap. This theorem does NOT certify that reference premise. -/
theorem planeWeakCos_conditional_gap (ell : ℝ) (hell : 0 < ell) (N : ℕ)
    (hgap : ∀ k ≤ N,
      (countablePairLift k planePairOperator * countablePairLift k planePairOperator -
        (1/25 : ℂ) • countablePairLift k planePairOperator).IsPositive) :
    ∀ t ∈ spectrum ℝ (planeWeakCosContactOperator ell hell N), t = 0 ∨ (3/100 : ℝ) ≤ t := by
  have h := physical_scalar_criterion ell hell planeWeakCos planeWeakCos_differentiable
    ((9999/10000 : ℝ)^2) ((10001/10000 : ℝ)^2) ((9999/10000 : ℝ)^4) (1/25)
    (by norm_num) (by norm_num) (by norm_num)
    (planeWeakCos_gram_bounds ell hell).1 (planeWeakCos_gram_bounds ell hell).2
    (planeWeakCos_coercivity ell) N (by simpa using hgap)
  intro t ht
  rcases h t ht with hz | hb
  · exact Or.inl hz
  · right
    have hc : (3/100 : ℝ) ≤ ((9999/10000 : ℝ)^4)/((9999/10000 : ℝ)^2)^2 *
        ((1/25 : ℝ)-14*(1-((9999/10000 : ℝ)^2)/((10001/10000 : ℝ)^2))-
          (1-((9999/10000 : ℝ)^2)/((10001/10000 : ℝ)^2))^2) := by norm_num
    exact hc.trans hb

end VortexGap.Fermion
