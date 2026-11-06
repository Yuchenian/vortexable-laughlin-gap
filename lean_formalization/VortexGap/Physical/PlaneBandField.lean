import VortexGap.Physical.PlaneMultiplication
import VortexGap.Physical.PlaneContactOperator
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory
open scoped ComplexOrder BoundedContinuousFunction

/-- Riesz evaluation vector in the actual multiplied LLL subspace of physical L2. -/
def planeBandEvaluation (ell : ℝ) (hell : 0 < ell) (f : ℂ →ᵇ ℂ)
    (hG : IsStrictlyPositive (planeScalarGram ell hell f)) (z : ℂ) :
    (planeScalarEmbedding ell hell f).toLinearMap.range :=
  planeScalarUnitary ell hell f hG ((starRingEnd ℂ) (f z) •
    gramInvSqrt (planeScalarEmbedding ell hell f) (planeEvaluation ell z))

theorem planeBandEvaluation_coefficient (ell : ℝ) (hell : 0 < ell) (f : ℂ →ᵇ ℂ)
    (hG : IsStrictlyPositive (planeScalarGram ell hell f)) (z : ℂ) (v : CountableOrbital) :
    inner ℂ (planeBandEvaluation ell hell f hG z) (planeScalarUnitary ell hell f hG v) =
      f z * inner ℂ (planeEvaluation ell z) (gramInvSqrt (planeScalarEmbedding ell hell f) v) := by
  rw [planeBandEvaluation, (planeScalarUnitary ell hell f hG).inner_map_map, inner_smul_left,
    starRingEnd_self_apply]
  rw [(ContinuousLinearMap.nonneg_iff_isPositive.mp
    (gramInvSqrt_nonneg (planeScalarEmbedding ell hell f) hG)).inner_left_eq_inner_right]

/-- The Riesz coefficients represent the actual ambient L2 wavefunctions, not
an assumed abstract copy of the band. -/
theorem planeBandEvaluation_represents (ell : ℝ) (hell : 0 < ell) (f : ℂ →ᵇ ℂ)
    (hG : IsStrictlyPositive (planeScalarGram ell hell f))
    (v : (planeScalarEmbedding ell hell f).toLinearMap.range) :
    (fun z => inner ℂ (planeBandEvaluation ell hell f hG z) v) =ᵐ[volume]
      (v : Lp ℂ 2 (volume : Measure ℂ)) := by
  have h := planeScalarUnitary_coe ell hell f hG ((planeScalarUnitary ell hell f hG).symm v)
  simp only [LinearIsometryEquiv.apply_symm_apply] at h
  filter_upwards [h] with z hz
  rw [hz]
  simpa only [LinearIsometryEquiv.apply_symm_apply] using
    planeBandEvaluation_coefficient ell hell f hG z ((planeScalarUnitary ell hell f hG).symm v)

/-- Physical annihilation in the orthonormal coordinates supplied by the proved
unitary onto the actual band range. -/
def planeBandAnnihilate (ell : ℝ) (hell : 0 < ell) (f : ℂ →ᵇ ℂ)
    (hG : IsStrictlyPositive (planeScalarGram ell hell f))
    (v : (planeScalarEmbedding ell hell f).toLinearMap.range) : CountableSpace →L[ℂ] CountableSpace :=
  countableAnnihilate ((planeScalarUnitary ell hell f hG).symm v)

theorem planeBandAnnihilate_car (ell : ℝ) (hell : 0 < ell) (f : ℂ →ᵇ ℂ)
    (hG : IsStrictlyPositive (planeScalarGram ell hell f))
    (u v : (planeScalarEmbedding ell hell f).toLinearMap.range) :
    planeBandAnnihilate ell hell f hG u * countableCreate ((planeScalarUnitary ell hell f hG).symm v) +
      countableCreate ((planeScalarUnitary ell hell f hG).symm v) * planeBandAnnihilate ell hell f hG u =
      inner ℂ u v • 1 := by
  rw [planeBandAnnihilate, countableOrbital_car, (planeScalarUnitary ell hell f hG).symm.inner_map_map]

def planeBandField (ell : ℝ) (hell : 0 < ell) (f : ℂ →ᵇ ℂ)
    (hG : IsStrictlyPositive (planeScalarGram ell hell f)) (z : ℂ) :
    CountableSpace →L[ℂ] CountableSpace :=
  planeBandAnnihilate ell hell f hG (planeBandEvaluation ell hell f hG z)

theorem planeBandField_eq_filtered (ell : ℝ) (hell : 0 < ell) (f : ℂ →ᵇ ℂ)
    (hG : IsStrictlyPositive (planeScalarGram ell hell f)) (z : ℂ) :
    planeBandField ell hell f hG z =
      f z • planeFilteredField (gramInvSqrt (planeScalarEmbedding ell hell f)) ell z := by
  simp only [planeBandField, planeBandAnnihilate, planeBandEvaluation,
    LinearIsometryEquiv.symm_apply_apply, countableAnnihilate_smul,
    starRingEnd_self_apply, planeFilteredField]

/-- Derivative contact built directly from the band evaluation field. -/
def planeBandContactDensity (ell : ℝ) (hell : 0 < ell) (f : ℂ →ᵇ ℂ)
    (hG : IsStrictlyPositive (planeScalarGram ell hell f))
    (z : ℂ) (N : ℕ) (x : countableSector N) : ℝ :=
  4*Real.pi*ell^4 *
    (‖(planeBandField ell hell f hG z *
      deriv (fun t : ℝ => planeBandField ell hell f hG (z+(t : ℂ)*1)) 0) x‖^2 +
     ‖(planeBandField ell hell f hG z *
      deriv (fun t : ℝ => planeBandField ell hell f hG (z+(t : ℂ)*Complex.I)) 0) x‖^2)

theorem planeBandContactDensity_eq (ell : ℝ) (hell : 0 < ell) (f : ℂ →ᵇ ℂ)
    (hG : IsStrictlyPositive (planeScalarGram ell hell f))
    (z : ℂ) (N : ℕ) (x : countableSector N) :
    planeBandContactDensity ell hell f hG z N x =
      planeScalarContactDensity (gramInvSqrt (planeScalarEmbedding ell hell f)) ell f z N x := by
  simp only [planeBandContactDensity, planeBandField_eq_filtered,
    planeScalarContactDensity, planeScalarContactField]

theorem planeBandContactDensity_integrable (ell : ℝ) (hell : 0 < ell) (f : ℂ →ᵇ ℂ)
    (hG : IsStrictlyPositive (planeScalarGram ell hell f)) (hf : Differentiable ℝ f)
    (N : ℕ) (x : countableSector N) :
    Integrable (fun z => planeBandContactDensity ell hell f hG z N x) := by
  simp_rw [planeBandContactDensity_eq]
  exact planeScalarContactDensity_integrable _ (gramInvSqrt_nonneg _ hG) ell hell f hf N x

theorem planeBandContactDensity_integral (ell : ℝ) (hell : 0 < ell) (f : ℂ →ᵇ ℂ)
    (hG : IsStrictlyPositive (planeScalarGram ell hell f)) (hf : Differentiable ℝ f)
    (N : ℕ) (x : countableSector N) :
    (∫ z, planeBandContactDensity ell hell f hG z N x) =
      (inner ℂ x (filteredPairHamiltonian N (gramInvSqrt (planeScalarEmbedding ell hell f))
        (gramInvSqrt_nonneg _ hG) (planeWeightedPairOperator ell f) x)).re := by
  simp_rw [planeBandContactDensity_eq]
  exact planeScalarContactEnergy_filteredPairLift _ (gramInvSqrt_nonneg _ hG) ell hell f hf N x

end VortexGap.Fermion
