import VortexGap.Physical.PlaneWeightedPair
import VortexGap.Frame.CountableBoundedFilter
import VortexGap.Physical.PairCoercivity
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory Filter VortexGap.Frame
open scoped ComplexOrder BoundedContinuousFunction

theorem planeWeightedPair_filtered_annihilation_norm
    (D : CountablePairSpace →L[ℂ] CountablePairSpace) (ell : ℝ) (f : ℂ →ᵇ ℂ)
    (a : ℂ) (N : ℕ) (x : countableSector N) :
    ‖countablePairAnnihilate N (D (planeWeightedPair ell f a)) x‖^2 =
      ‖f ((Real.sqrt 2*ell : ℝ) • (starRingEnd ℂ) a)‖^4 *
        ‖countablePairAnnihilate N (D (countableTwoFramePair (planeTwoFrame a))) x‖^2 := by
  simp only [planeWeightedPair, map_smul, countablePairAnnihilate_smul,
    smul_apply, norm_smul, Complex.norm_conj, mul_pow, planeContactWeightRoot_norm, ← pow_mul]

/-- Representation of the actual independently defined physical contact integral.
The inverse-Gram filter is permitted to have norm greater than one. -/
theorem planeScalarContactEnergy_filteredPairLift
    (R : CountableOrbital →L[ℂ] CountableOrbital) (hR : 0 ≤ R)
    (ell : ℝ) (hell : 0 < ell) (f : ℂ →ᵇ ℂ) (hf : Differentiable ℝ f)
    (N : ℕ) (x : countableSector N) :
    planeScalarContactEnergy R ell f N x =
      (inner ℂ x (filteredPairHamiltonian N R hR (planeWeightedPairOperator ell f) x)).re := by
  rw [planeScalarContactEnergy_pair R hR ell hell f hf N x]
  have h := countableBoundedFilter_energy planePairMeasure (planeWeightedPair ell f)
    (planeWeightedPair_coefficient_memLp ell f) (‖f‖^4) (by positivity)
    (planeWeightedPair_bessel ell f) (countablePairFilter R hR)
    (spanningSets planePairMeasure)
    (increasingCutoffs_aecover planePairMeasure (spanningSets planePairMeasure)
      (measurableSet_spanningSets planePairMeasure) (monotone_spanningSets planePairMeasure)
      (iUnion_spanningSets planePairMeasure))
    (planeWeightedPair_spanning_memLp ell f) (monotone_spanningSets planePairMeasure)
    (iUnion_spanningSets planePairMeasure) N x
  simp_rw [planeWeightedPair_filtered_annihilation_norm] at h
  simpa only [filteredPairHamiltonian, planeWeightedPairOperator, countablePairFilter_adjoint] using h

theorem planeScalarContactOperator_exists
    (R : CountableOrbital →L[ℂ] CountableOrbital) (hR : 0 ≤ R)
    (ell : ℝ) (hell : 0 < ell) (f : ℂ →ᵇ ℂ) (hf : Differentiable ℝ f) (N : ℕ) :
    ∃ A : countableSector N →L[ℂ] countableSector N, A.IsPositive ∧
      ∀ x, planeScalarContactEnergy R ell f N x = (inner ℂ x (A x)).re := by
  exact ⟨filteredPairHamiltonian N R hR (planeWeightedPairOperator ell f),
    filteredPairHamiltonian_positive N R hR _ (planeWeightedPairOperator_positive ell f),
    planeScalarContactEnergy_filteredPairLift R hR ell hell f hf N⟩

/-- Positive bounded representative of the independently defined derivative-contact
quadratic form. Existence is proved above; no pullback identity is an input. -/
def planeScalarContactOperator
    (R : CountableOrbital →L[ℂ] CountableOrbital) (hR : 0 ≤ R)
    (ell : ℝ) (hell : 0 < ell) (f : ℂ →ᵇ ℂ) (hf : Differentiable ℝ f) (N : ℕ) :
    countableSector N →L[ℂ] countableSector N :=
  (planeScalarContactOperator_exists R hR ell hell f hf N).choose

theorem planeScalarContactOperator_positive
    (R : CountableOrbital →L[ℂ] CountableOrbital) (hR : 0 ≤ R)
    (ell : ℝ) (hell : 0 < ell) (f : ℂ →ᵇ ℂ) (hf : Differentiable ℝ f) (N : ℕ) :
    (planeScalarContactOperator R hR ell hell f hf N).IsPositive :=
  (planeScalarContactOperator_exists R hR ell hell f hf N).choose_spec.1

theorem planeScalarContactOperator_energy
    (R : CountableOrbital →L[ℂ] CountableOrbital) (hR : 0 ≤ R)
    (ell : ℝ) (hell : 0 < ell) (f : ℂ →ᵇ ℂ) (hf : Differentiable ℝ f)
    (N : ℕ) (x : countableSector N) :
    planeScalarContactEnergy R ell f N x =
      (inner ℂ x (planeScalarContactOperator R hR ell hell f hf N x)).re :=
  (planeScalarContactOperator_exists R hR ell hell f hf N).choose_spec.2 x

theorem planeScalarContactOperator_unique
    (R : CountableOrbital →L[ℂ] CountableOrbital) (hR : 0 ≤ R)
    (ell : ℝ) (hell : 0 < ell) (f : ℂ →ᵇ ℂ) (hf : Differentiable ℝ f) (N : ℕ)
    (A : countableSector N →L[ℂ] countableSector N) (hA : A.IsPositive)
    (he : ∀ x, planeScalarContactEnergy R ell f N x = (inner ℂ x (A x)).re) :
    A = planeScalarContactOperator R hR ell hell f hf N := by
  apply ContinuousLinearMap.coe_injective
  apply (ext_inner_map _ _).mp
  intro x
  have hB := planeScalarContactOperator_positive R hR ell hell f hf N
  rw [← hA.toLinearMap.isSymmetric.coe_re_inner_apply_self,
    ← hB.toLinearMap.isSymmetric.coe_re_inner_apply_self]
  congr 1
  change (inner ℂ (A x) x).re =
    (inner ℂ (planeScalarContactOperator R hR ell hell f hf N x) x).re
  calc
    _ = (inner ℂ x (A x)).re := inner_re_symm (𝕜 := ℂ) (A x) x
    _ = planeScalarContactEnergy R ell f N x := (he x).symm
    _ = (inner ℂ x (planeScalarContactOperator R hR ell hell f hf N x)).re :=
      planeScalarContactOperator_energy R hR ell hell f hf N x
    _ = _ := inner_re_symm (𝕜 := ℂ) x (planeScalarContactOperator R hR ell hell f hf N x)

theorem planeScalarContactOperator_eq_pairLift
    (R : CountableOrbital →L[ℂ] CountableOrbital) (hR : 0 ≤ R)
    (ell : ℝ) (hell : 0 < ell) (f : ℂ →ᵇ ℂ) (hf : Differentiable ℝ f) (N : ℕ) :
    planeScalarContactOperator R hR ell hell f hf N =
      filteredPairHamiltonian N R hR (planeWeightedPairOperator ell f) := by
  exact (planeScalarContactOperator_unique R hR ell hell f hf N _
    (filteredPairHamiltonian_positive N R hR _ (planeWeightedPairOperator_positive ell f))
    (planeScalarContactEnergy_filteredPairLift R hR ell hell f hf N)).symm

end VortexGap.Fermion
