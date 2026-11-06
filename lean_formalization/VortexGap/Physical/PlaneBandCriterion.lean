import VortexGap.Physical.PlaneBandField
import VortexGap.Physical.PlaneWeightedBounds
import VortexGap.Physical.GramFilter
import VortexGap.Physical.CoercivityGap
import VortexGap.Transfer.PlaneTransfer
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory
open scoped ComplexOrder BoundedContinuousFunction

def planeBandContactOperator (ell : ℝ) (hell : 0 < ell) (f : ℂ →ᵇ ℂ)
    (hG : IsStrictlyPositive (planeScalarGram ell hell f)) (hf : Differentiable ℝ f) (N : ℕ) :
    countableSector N →L[ℂ] countableSector N :=
  planeScalarContactOperator (gramInvSqrt (planeScalarEmbedding ell hell f))
    (gramInvSqrt_nonneg _ hG) ell hell f hf N

theorem planeBandContactOperator_energy (ell : ℝ) (hell : 0 < ell) (f : ℂ →ᵇ ℂ)
    (hG : IsStrictlyPositive (planeScalarGram ell hell f)) (hf : Differentiable ℝ f)
    (N : ℕ) (x : countableSector N) :
    (inner ℂ x (planeBandContactOperator ell hell f hG hf N x)).re =
      ∫ z, planeBandContactDensity ell hell f hG z N x := by
  rw [planeBandContactDensity_integral ell hell f hG hf N x,
    planeBandContactOperator, planeScalarContactOperator_eq_pairLift]

theorem planeBandContactOperator_positive (ell : ℝ) (hell : 0 < ell) (f : ℂ →ᵇ ℂ)
    (hG : IsStrictlyPositive (planeScalarGram ell hell f)) (hf : Differentiable ℝ f) (N : ℕ) :
    (planeBandContactOperator ell hell f hG hf N).IsPositive :=
  planeScalarContactOperator_positive _ _ _ _ _ _ _

/-- Physical scalar-band criterion. All plane geometry and concrete CAR loss inputs
are proved; only the original sector gaps and projected coercivity are supplied. -/
theorem planeBandContact_kernel_gap (ell : ℝ) (hell : 0 < ell) (f : ℂ →ᵇ ℂ)
    (hG : IsStrictlyPositive (planeScalarGram ell hell f)) (hf : Differentiable ℝ f)
    (g u κ γ : ℝ) (hg : 0 < g) (hgu : g ≤ u) (hκ : 0 < κ)
    (hlo : g • (1 : CountableOrbital →L[ℂ] CountableOrbital) ≤ planeScalarGram ell hell f)
    (hhi : planeScalarGram ell hell f ≤ u • (1 : CountableOrbital →L[ℂ] CountableOrbital))
    (hw : (κ : ℂ) • planePairOperator ≤ planeWeightedPairOperator ell f)
    (N : ℕ) (hgap : ∀ k ≤ N,
      (countablePairLift k planePairOperator * countablePairLift k planePairOperator -
        (γ : ℂ) • countablePairLift k planePairOperator).IsPositive) :
    let R := gramInvSqrt (planeScalarEmbedding ell hell f)
    let hR := gramInvSqrt_nonneg (planeScalarEmbedding ell hell f) hG
    let M := (Real.sqrt g : ℂ) • R
    let hM : 0 ≤ M := smul_nonneg
      (show 0 ≤ (Real.sqrt g : ℂ) by exact_mod_cast Real.sqrt_nonneg g) hR
    let A := planeBandContactOperator ell hell f hG hf N
    LinearMap.ker A.toLinearMap = LinearMap.ker (filteredPairHamiltonian N M hM planePairOperator).toLinearMap ∧
      ∀ x ∈ (LinearMap.ker A.toLinearMap)ᗮ,
        (κ/g^2*(γ-14*(1-g/u)-(1-g/u)^2))*‖x‖^2 ≤ (inner ℂ x (A x)).re := by
  dsimp only
  let R := gramInvSqrt (planeScalarEmbedding ell hell f)
  have hR : 0 ≤ R := gramInvSqrt_nonneg _ hG
  let M := (Real.sqrt g : ℂ) • R
  have hM : 0 ≤ M := smul_nonneg
    (show 0 ≤ (Real.sqrt g : ℂ) by exact_mod_cast Real.sqrt_nonneg g) hR
  have he : gramFilter (planeScalarGram ell hell f) g = M := by
    rw [planeScalarGram, gramFilter_eq_normalized_inverse]
    ext v
    rfl
  have hMc : ‖M‖ ≤ 1 := by
    simpa only [he] using gramFilter_contraction (planeScalarGram ell hell f) g hg hlo
  have hd : ‖1-M^2‖ ≤ 1-g/u := by
    simpa only [he] using gramFilter_loss_le (planeScalarGram ell hell f) g u hg hgu hlo hhi
  have ht := plane_filtered_transfer M hM hMc γ N hgap
  have hrep : filteredPairHamiltonian N M hM planePairOperator = planeFilteredHamiltonian M hM N :=
    filteredPairHamiltonian_eq_continuous _ _ _ _ _ _ M hM N
  dsimp only at ht
  rw [← hrep] at ht
  have hc := filtered_coercivity_kernel_gap N R hR planePairOperator (planeWeightedPairOperator ell f)
    (ContinuousLinearMap.nonneg_iff_isPositive.mpr planePairOperator_positive)
    κ (‖f‖^4) g (γ-14*‖1-M^2‖-‖1-M^2‖^2) hκ hg hw
    (by simpa only [Complex.ofReal_pow] using planeWeightedPairOperator_upper ell f) ht
  simp only [planeBandContactOperator, planeScalarContactOperator_eq_pairLift]
  refine ⟨hc.1, ?_⟩
  intro x hx
  have hdec : γ-14*(1-g/u)-(1-g/u)^2 ≤ γ-14*‖1-M^2‖-‖1-M^2‖^2 := by
    nlinarith [norm_nonneg (1-M^2)]
  have hk : 0 ≤ κ/g^2 := le_of_lt (div_pos hκ (sq_pos_of_pos hg))
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdec hk) (sq_nonneg ‖x‖)).trans (hc.2 x hx)

end VortexGap.Fermion
