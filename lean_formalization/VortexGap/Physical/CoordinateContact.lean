import VortexGap.Geometry.CoordinateChange
import VortexGap.Physical.PlaneBandSpectrum
import VortexGap.Physical.PlaneContactNormalization

noncomputable section

namespace VortexGap.Fermion
open MeasureTheory VortexGap.Frame
open scoped BoundedContinuousFunction ComplexOrder

def coordinateField (F : ℂ ≃ₜ ℂ) (ell : ℝ) (z : ℂ) :=
  ((Real.sqrt (coordinateJacobian F z) : ℝ) : ℂ) • planeFilteredField 1 ell (F z)

def coordinateContact (F : ℂ ≃ₜ ℂ) (ell : ℝ) (z c : ℂ) :=
  coordinateField F ell z * deriv (fun s : ℝ => coordinateField F ell (z+(s:ℂ)*c)) 0

theorem coordinateContact_cancel (F : ℂ ≃ₜ ℂ) (hf : ContDiff ℝ 2 F)
    (hJ : ∀ z, 0 < coordinateJacobian F z) (ell : ℝ) (z c : ℂ) :
    coordinateContact F ell z c = (coordinateJacobian F z : ℂ) •
      (planeFilteredField 1 ell (F z) * planeFilteredFieldDerivative 1 ell (F z) (fderiv ℝ F z c)) := by
  let p := fun s : ℝ => z+(s:ℂ)*c
  have hp : HasDerivAt p c 0 := by simpa [p] using (Complex.ofRealCLM.hasDerivAt.mul_const c).const_add z
  have hz : p 0 = z := by simp [p]
  have hF := ((hf.differentiable (by decide)) (p 0)).hasFDerivAt.comp_hasDerivAt 0 hp
  have hχ := planeFilteredField_hasDerivAt_curve 1 ell (fun s => F (p s)) _ 0 hF
  have hs := (Complex.ofRealCLM.differentiableAt.comp (p 0)
    (((coordinateJacobian_diff F hf) (p 0)).sqrt (hJ _).ne')).hasFDerivAt.comp_hasDerivAt 0 hp
  have h := differentiable_contact_cancel (fun s => planeFilteredField 1 ell (F (p s))) _
    (fun s => ((Real.sqrt (coordinateJacobian F (p s)) : ℝ) : ℂ)) _ 0 _ hχ hs rfl
  rw [hz, ← Complex.ofReal_pow, Real.sq_sqrt (hJ _).le] at h
  exact h

def coordinateDensity (F : ℂ ≃ₜ ℂ) (ell : ℝ) (z : ℂ) (N : ℕ) (x : countableSector N) :=
  4*Real.pi*ell^4*(‖coordinateContact F ell z 1 x‖^2 + ‖coordinateContact F ell z Complex.I x‖^2)

theorem coordinateDensity_reference (F : ℂ ≃ₜ ℂ) (hf : ContDiff ℝ 2 F)
    (hJ : ∀ z, 0 < coordinateJacobian F z) (ell : ℝ) (hell : 0 < ell)
    (z : ℂ) (N : ℕ) (x : countableSector N) :
    coordinateDensity F ell z N x = coordinateJacobian F z * (coordinateMetricWeight F (F z) *
      planeScalarContactDensity 1 ell (fun _ => 1) (F z) N x) := by
  rw [planeScalarContactDensity_pair 1 zero_le_one ell hell _ _ (differentiableAt_const _) N x]
  simp only [coordinateDensity,coordinateContact_cancel F hf hJ,smul_apply,norm_smul,mul_pow,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hJ _),coordinateMetricWeight,F.symm_apply_apply,
    norm_one,one_pow,one_mul]
  simp_rw [planeFilteredField_contact_pair 1 zero_le_one, norm_smul, mul_pow,
    planeContactCoefficient_norm_sq ell hell]
  field_simp
  ring

theorem coordinateEnergy_reference (F : ℂ ≃ₜ ℂ) (hf : ContDiff ℝ 2 F)
    (hJ : ∀ z, 0 < coordinateJacobian F z) (ell : ℝ) (hell : 0 < ell)
    (N : ℕ) (x : countableSector N) :
    (∫ z, coordinateDensity F ell z N x) =
      ∫ w, coordinateMetricWeight F w * planeScalarContactDensity 1 ell (fun _ => 1) w N x := by
  simp_rw [coordinateDensity_reference F hf hJ ell hell]
  exact coordinateChange_integral F (hf.differentiable (by decide)) hJ (fun w => coordinateMetricWeight F w * planeScalarContactDensity 1 ell (fun _ => 1) w N x)

private def metricSymbol (F : ℂ ≃ₜ ℂ) (hf : ContDiff ℝ 2 F) (b : ℝ)
    (hb : ∀ z, coordinateMetricWeight F z ≤ b) : ℂ →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun z => ((Real.sqrt (Real.sqrt (coordinateMetricWeight F z)) : ℝ) : ℂ))
    (Complex.continuous_ofReal.comp ((coordinateMetricWeight_continuous F hf).sqrt.sqrt))
    (Real.sqrt (Real.sqrt b)) (fun z => by
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
      exact Real.sqrt_le_sqrt (Real.sqrt_le_sqrt (hb z)))

private theorem metricSymbol_weight (F : ℂ ≃ₜ ℂ) (hf : ContDiff ℝ 2 F) (b : ℝ)
    (hb : ∀ z, coordinateMetricWeight F z ≤ b) (z : ℂ) (hz : 0 ≤ coordinateMetricWeight F z) :
    ‖metricSymbol F hf b hb z‖^4 = coordinateMetricWeight F z := by
  change ‖((Real.sqrt (Real.sqrt _) : ℝ) : ℂ)‖^4 = _
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),
    show (4:ℕ)=2*2 by decide,pow_mul,Real.sq_sqrt (Real.sqrt_nonneg _),Real.sq_sqrt hz]

private theorem weighted_reference_energy (ell : ℝ) (hell : 0 < ell) (f : ℂ →ᵇ ℂ)
    (N : ℕ) (x : countableSector N) :
    (∫ z, ‖f z‖^4 * planeScalarContactDensity 1 ell (fun _ => 1) z N x) =
      (inner ℂ x (countablePairLift N (planeWeightedPairOperator ell f) x)).re := by
  simp_rw [planeScalarContactDensity_pair 1 zero_le_one ell hell _ _ (differentiableAt_const _) N x,
    norm_one,one_pow,one_mul, ← mul_assoc]
  rw [planeContact_integral_weight ell hell (fun z => ‖f z‖^4) (fun a => ‖countablePairAnnihilate N
    (countablePairFilter 1 zero_le_one (countableTwoFramePair (planeTwoFrame a))) x‖^2)]
  have h := countableBoundedFilter_energy planePairMeasure (planeWeightedPair ell f)
    (planeWeightedPair_coefficient_memLp ell f) (‖f‖^4) (by positivity)
    (planeWeightedPair_bessel ell f) (countablePairFilter 1 zero_le_one)
    (spanningSets planePairMeasure)
    (increasingCutoffs_aecover planePairMeasure (spanningSets planePairMeasure)
      (measurableSet_spanningSets planePairMeasure) (monotone_spanningSets planePairMeasure)
      (iUnion_spanningSets planePairMeasure))
    (planeWeightedPair_spanning_memLp ell f) (monotone_spanningSets planePairMeasure)
    (iUnion_spanningSets planePairMeasure) N x
  simp_rw [planeWeightedPair_filtered_annihilation_norm] at h
  simp_rw [countablePairFilter_adjoint] at h
  have hid : (1 : CountablePairSpace →L[ℂ] CountablePairSpace) = ContinuousLinearMap.id ℂ _ := rfl
  simpa [planeWeightedPairOperator,planeContact_identity_filter,hid] using! h

theorem coordinatePhysical_kernel_gap (F : ℂ ≃ₜ ℂ) (hf : ContDiff ℝ 2 F)
    (hJ : ∀ z, 0 < coordinateJacobian F z) (a b : ℝ) (ha : 0 < a)
    (hw : ∀ z, a ≤ coordinateMetricWeight F z ∧ coordinateMetricWeight F z ≤ b)
    (ell : ℝ) (hell : 0 < ell) (N : ℕ) (γ : ℝ)
    (href : let H := countablePairLift N planePairOperator
      (H*H-(γ:ℂ) • H).IsPositive) :
    ∃ A : countableSector N →L[ℂ] countableSector N, A.IsPositive ∧
      (∀ x, (inner ℂ x (A x)).re = ∫ z, coordinateDensity F ell z N x) ∧
      LinearMap.ker A.toLinearMap = LinearMap.ker (countablePairLift N planePairOperator).toLinearMap ∧
      ∀ s ∈ spectrum ℝ A, s = 0 ∨ a*γ ≤ s := by
  let f := metricSymbol F hf b (fun z => (hw z).2)
  have he z : ‖f z‖^4 = coordinateMetricWeight F z := metricSymbol_weight F hf b _ z (ha.le.trans (hw z).1)
  let A := countablePairLift N (planeWeightedPairOperator ell f)
  let B := countablePairLift N planePairOperator
  have hA := countablePairLift_positive N _ (planeWeightedPairOperator_positive ell f)
  have posA : 0 ≤ A := ContinuousLinearMap.nonneg_iff_isPositive.mpr hA
  have posB : 0 ≤ B := ContinuousLinearMap.nonneg_iff_isPositive.mpr (countablePairLift_positive N _ planePairOperator_positive)
  have hl : (a:ℂ) • B ≤ A := by
    rw [← countablePairLift_smul]; apply countablePairLift_mono N
    exact planeWeightedPairOperator_lower ell f a ha.le (fun z => (hw z).1.trans_eq (he z).symm)
  have hu : A ≤ ((‖f‖^4 : ℝ):ℂ) • B := by
    rw [← countablePairLift_smul]; apply countablePairLift_mono N
    simpa only [Complex.ofReal_pow] using planeWeightedPairOperator_upper ell f
  have hlo := operator_scaled_le_energy B A a hl
  have hhi := operator_le_scaled_energy A B _ hu
  refine ⟨A,hA,?_,positive_form_comparison_kernel A B posA posB a _ ha hlo hhi,
    kernel_complement_gap_spectrum A posA _ (positive_form_comparison_of_quadratic_gap A B posA posB
      a _ γ ha hlo hhi href)⟩
  intro x
  rw [coordinateEnergy_reference F hf hJ ell hell, ← weighted_reference_energy ell hell f N x]
  simp_rw [he]

end VortexGap.Fermion
