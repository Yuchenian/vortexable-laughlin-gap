import VortexGap.Physical.PlaneContactNormalization
import VortexGap.Geometry.PeriodicShear
import VortexGap.Physical.PlaneBandSpectrum
import VortexGap.Examples.PlaneBandDistinct

noncomputable section

namespace VortexGap.Fermion
open MeasureTheory
open scoped ComplexOrder BoundedContinuousFunction

def shearContactField (a k ell : ℝ) (z c : ℂ) : CountableSpace →L[ℂ] CountableSpace :=
  planeFilteredField 1 ell (periodicShear a k z) *
    deriv (fun t : ℝ => planeFilteredField 1 ell (periodicShear a k (z+(t:ℂ)*c))) 0

def shearPhysicalDensity (a k ell : ℝ) (z : ℂ) (N : ℕ) (x : countableSector N) : ℝ :=
  4*Real.pi*ell^4 * (‖shearContactField a k ell z 1 x‖^2 +
                        ‖shearContactField a k ell z Complex.I x‖^2)

private theorem shear_field_curve (a k ell : ℝ) (z c d : ℂ)
    (h : HasDerivAt (fun t : ℝ => periodicShear a k (z+(t:ℂ)*c)) d 0) :
    shearContactField a k ell z c = planeFilteredField 1 ell (periodicShear a k z) *
      planeFilteredFieldDerivative 1 ell (periodicShear a k z) d := by
  have ht := (planeFilteredField_hasDerivAt_curve 1 ell _ d 0 h).deriv
  simpa [shearContactField, ht]

theorem shearPhysicalDensity_pair (a k ell : ℝ) (hk : k ≠ 0) (hell : 0 < ell)
    (z : ℂ) (N : ℕ) (x : countableSector N) :
    shearPhysicalDensity a k ell z N x = periodicShearWeight a k z *
      (1/(Real.pi*ell^2)) * ‖countablePairAnnihilate N (countablePairFilter 1 zero_le_one
        (countableTwoFramePair (planeTwoFrame ((starRingEnd ℂ) (planeCoordinate ell (periodicShear a k z)))))) x‖^2 := by
  let d : ℂ := ((a*Real.cos (k*z.im) : ℝ) : ℂ) + Complex.I
  have hx : HasDerivAt (fun t : ℝ => periodicShear a k (z+(t:ℂ)*1)) 1 0 := by
    simpa using periodicShear_horizontal a k z
  have hy := periodicShear_vertical a k hk z
  rw [shearPhysicalDensity, shear_field_curve a k ell z 1 1 hx,
    shear_field_curve a k ell z Complex.I d hy]
  simp_rw [planeFilteredField_contact_pair 1 zero_le_one, norm_smul, mul_pow,
    planeContactCoefficient_norm_sq ell hell]
  rw [← periodicShear_contact_weight]
  dsimp only [d]
  field_simp
  ring

theorem shearPairSymbol_differentiable (a k : ℝ) : Differentiable ℝ (periodicShearPairSymbol a k) := by
  intro z
  have hp : 0 < periodicShearWeight a k z := by linarith [(periodicShearWeight_bounds a k z).1]
  have hw : DifferentiableAt ℝ (periodicShearWeight a k) z := by unfold periodicShearWeight; fun_prop
  exact Complex.ofRealCLM.differentiableAt.comp z ((hw.sqrt hp.ne').sqrt (Real.sqrt_pos.2 hp).ne')

def shearHamiltonian (a k ell : ℝ) (hell : 0 < ell) (N : ℕ) :=
  planeScalarContactOperator 1 zero_le_one ell hell (periodicShearPairSymbol a k)
    (shearPairSymbol_differentiable a k) N

theorem shearHamiltonian_energy (a k ell : ℝ) (hk : k ≠ 0) (hell : 0 < ell)
    (N : ℕ) (x : countableSector N) :
    (inner ℂ x (shearHamiltonian a k ell hell N x)).re = ∫ z, shearPhysicalDensity a k ell z N x := by
  rw [shearHamiltonian, ← planeScalarContactOperator_energy, planeScalarContactEnergy]
  let F := periodicShearEquiv a k
  have hF : MeasurePreserving F := periodicShear_preserves_area a k
  rw [← hF.integral_comp']
  apply integral_congr_ae
  filter_upwards with z
  rw [planeScalarContactDensity_pair 1 zero_le_one ell hell _ _ (shearPairSymbol_differentiable a k _) N x,
    periodicShearPairSymbol_fourth, shearPhysicalDensity_pair a k ell hk hell]
  rfl

theorem shearHamiltonian_comparison (a k ell : ℝ) (hk : k ≠ 0) (hell : 0 < ell)
    (N : ℕ) (x : countableSector N) :
    let E := (inner ℂ x (shearHamiltonian a k ell hell N x)).re
    let E₀ := (inner ℂ x (countablePairLift N planePairOperator x)).re
    E₀ ≤ E ∧ E ≤ (1+a^2/2)*E₀ := by
  let d := fun z => planeScalarContactDensity 1 ell (fun _ => 1) z N x
  have hd : Integrable d := planeScalarContactDensity_integrable 1 zero_le_one ell hell
    (1 : ℂ →ᵇ ℂ) (differentiable_const 1) N x
  have hpos (z) : 0 ≤ d z := by unfold d planeScalarContactDensity; positivity
  have h0 : (∫ z, d z) = (inner ℂ x (countablePairLift N planePairOperator x)).re := by
    simpa [d, planeScalarContactEnergy] using planeScalarContactEnergy_constant ell hell 1 N x
  have hw (z) : shearPhysicalDensity a k ell z N x = periodicShearWeight a k z * d (periodicShear a k z) := by
    rw [shearPhysicalDensity_pair a k ell hk hell]
    dsimp only [d]
    rw [planeScalarContactDensity_pair 1 zero_le_one ell hell _ _ (differentiableAt_const _) N x]
    simp [mul_assoc]
  dsimp only
  rw [shearHamiltonian_energy a k ell hk hell, ← h0]
  simp_rw [hw]
  exact periodicShear_integral_comparison a k d hd hpos

/-- Arbitrary shear amplitude: equality of the full kernels and inheritance of
the reference gap in the same particle-number sector. -/
theorem shearPhysical_kernel_gap (a k ell : ℝ) (hk : k ≠ 0) (hell : 0 < ell) (N : ℕ)
    (γ : ℝ) (href : let H := countablePairLift N planePairOperator
      (H*H-(γ:ℂ) • H).IsPositive) :
    LinearMap.ker (shearHamiltonian a k ell hell N).toLinearMap =
      LinearMap.ker (countablePairLift N planePairOperator).toLinearMap ∧
    ∀ t ∈ spectrum ℝ (shearHamiltonian a k ell hell N), t = 0 ∨ γ ≤ t := by
  let A := shearHamiltonian a k ell hell N
  let B := countablePairLift N planePairOperator
  have hA : 0 ≤ A := ContinuousLinearMap.nonneg_iff_isPositive.mpr
    (planeScalarContactOperator_positive ..)
  have hB : 0 ≤ B := ContinuousLinearMap.nonneg_iff_isPositive.mpr
    (countablePairLift_positive N _ planePairOperator_positive)
  have hl (x : countableSector N) : 1*(inner ℂ x (B x)).re ≤ (inner ℂ x (A x)).re := by
    rw [one_mul]; exact (shearHamiltonian_comparison a k ell hk hell N x).1
  have hu (x : countableSector N) :
      (inner ℂ x (A x)).re ≤ (1+a^2/2)*(inner ℂ x (B x)).re :=
    (shearHamiltonian_comparison a k ell hk hell N x).2
  refine ⟨positive_form_comparison_kernel A B hA hB 1 _ zero_lt_one hl hu, ?_⟩
  apply kernel_complement_gap_spectrum A hA γ
  simpa only [one_mul] using positive_form_comparison_of_quadratic_gap A B hA hB 1 _ γ zero_lt_one hl hu href

end VortexGap.Fermion

namespace VortexGap.Fermion
open MeasureTheory
open scoped BoundedContinuousFunction

def shearBandEmbedding (a k ell : ℝ) (hell : 0 < ell) :=
  (periodicShearUnitary a k).toLinearIsometry.comp (planeLLLEmbedding ell hell)

theorem shearBandEmbedding_coe (a k ell : ℝ) (hell : 0 < ell) (v : CountableOrbital) :
    (shearBandEmbedding a k ell hell v : ℂ → ℂ) =ᵐ[volume]
      fun z => inner ℂ (planeEvaluation ell (periodicShear a k z)) v :=
  (periodicShearUnitary_apply a k _).trans
    ((periodicShear_preserves_area a k).quasiMeasurePreserving.ae_eq_comp (planeLLLEmbedding_coe ell hell v))

private theorem shearKet (a k ell : ℝ) (hell : 0 < ell) (j : ℕ) :
    (shearBandEmbedding a k ell hell (orbitalKet j) : ℂ → ℂ) =ᵐ[volume]
      fun z => planeWavefunction ell (periodicShear a k z) j := by
  filter_upwards [shearBandEmbedding_coe a k ell hell (orbitalKet j)] with z hz
  rw [hz, ← inner_conj_symm, orbitalKet_inner_left, planeEvaluation_coefficient]
  simp

theorem shearBand_not_scalar (a k ell : ℝ) (ha : a ≠ 0) (hk : k ≠ 0) (hell : 0 < ell)
    (f : ℂ →ᵇ ℂ) :
    ¬ (shearBandEmbedding a k ell hell).toLinearMap.range ≤
      (planeScalarEmbedding ell hell f).toLinearMap.range := by
  intro h
  let F := periodicShear a k
  let vac := fun z => planeWavefunction ell (F z) 0
  let s : ℂ := ((Real.sqrt 2 * ell : ℝ) : ℂ)
  have hs : s ≠ 0 := by dsimp [s]; exact_mod_cast (show Real.sqrt 2 * ell ≠ 0 by positivity)
  have hv (z) : vac z ≠ 0 := by
    simp only [vac,planeWavefunction, planeBargmannCoeff, pow_zero, Nat.factorial_zero,
      Nat.cast_one, Real.sqrt_one, Complex.ofReal_one, div_one, mul_one]
    apply mul_ne_zero
    · exact_mod_cast inv_ne_zero (ne_of_gt (Real.sqrt_pos.2 (by positivity : 0 < 2*Real.pi*ell^2)))
    · exact Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
  let b := fun (v : CountableOrbital) z => inner ℂ (star v) (planeBargmann (planeCoordinate ell z))
  have hb (v) : Differentiable ℂ (b v) := by
    apply (innerSL ℂ (star v)).differentiable.comp
    apply (show Differentiable ℂ planeBargmann from fun z => (planeBargmann_hasDerivAt z).differentiableAt).comp
    unfold planeCoordinate; fun_prop
  have rep (j : ℕ) : ∃ v, ∀ᵐ z ∂volume, planeWavefunction ell (F z) j =
      (f z * planeWavefunction ell z 0) * b v z := by
    obtain ⟨v,hv⟩ := h (show shearBandEmbedding a k ell hell (orbitalKet j) ∈ _ from ⟨_,rfl⟩)
    change planeScalarEmbedding ell hell f v = shearBandEmbedding a k ell hell (orbitalKet j) at hv
    refine ⟨v,?_⟩
    filter_upwards [shearKet a k ell hell j, planeScalarEmbedding_coe ell hell f v] with z hz hf
    rw [hv,hz,planeEvaluation_gaussian_factor] at hf
    exact hf.trans (mul_assoc ..).symm
  obtain ⟨u,hu⟩ := rep 0
  obtain ⟨v,hv'⟩ := rep 1
  apply periodicShear_no_common_scalar ha hk vac (Filter.Eventually.of_forall hv)
  refine ⟨_,b u,fun z => s*b v z,hb u,(differentiable_const s).mul (hb v),hu,?_⟩
  filter_upwards [hv'] with z hz
  have hz' : F z * vac z = s * planeWavefunction ell (F z) 1 := by
    simp only [vac,planeWavefunction,planeBargmannCoeff,pow_zero,pow_one,Nat.factorial_one,
      Nat.factorial_zero,Nat.cast_one,Real.sqrt_one,Complex.ofReal_one,div_one,mul_one]
    change _ = s * (_ * (F z / s))
    field_simp
  rw [hz',hz]; ring

end VortexGap.Fermion
