import VortexGap.Physical.OrbitalColumn
import VortexGap.Physical.PlaneMultiplication
import VortexGap.Physical.PlaneBandSpectrum

noncomputable section

namespace VortexGap.Fermion
open MeasureTheory
open scoped BoundedContinuousFunction
variable {ι : Type*} [Fintype ι] [Nonempty ι]
local notation "V" => EuclideanSpace ℂ ι

def columnEnvelope (t : ℂ →ᵇ V) : ℂ →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun z => (‖t z‖ : ℂ))
    (Complex.continuous_ofReal.comp t.continuous.norm) ‖t‖ (fun z => by
      simpa only [Complex.norm_real, Real.norm_eq_abs, abs_norm] using t.norm_coe_le_norm z)

private def columnDirection (t : ℂ →ᵇ V) (z : ℂ) : V :=
  open Classical in if t z = 0 then EuclideanSpace.single (Classical.choice ‹Nonempty ι›) 1
  else (‖t z‖⁻¹ : ℝ) • t z

private theorem direction_norm (t : ℂ →ᵇ V) (z : ℂ) : ‖columnDirection t z‖ = 1 := by
  classical
  unfold columnDirection
  split_ifs with h
  · simp
  · simp [norm_smul,h]

private theorem direction_measurable (t : ℂ →ᵇ V) : Measurable (columnDirection t) := by
  classical
  apply Measurable.ite (measurableSet_eq_fun t.continuous.measurable measurable_const)
    measurable_const
  exact t.continuous.norm.measurable.inv.smul t.continuous.measurable

theorem columnEnvelope_factor (t : ℂ →ᵇ V) (z : ℂ) :
    columnEnvelope t z • columnDirection t z = t z := by
  classical
  change (‖t z‖ : ℂ) • _ = _
  change ‖t z‖ • columnDirection t z = t z
  unfold columnDirection
  split_ifs with h
  · simp [h]
  · rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr h),one_smul]

def columnPlaneEmbedding (ell : ℝ) (hell : 0 < ell) (t : ℂ →ᵇ V) :=
  (orbitalColumnIsometry (μ := (volume : Measure ℂ)) (columnDirection t)
    (direction_measurable t).aestronglyMeasurable (Filter.Eventually.of_forall (direction_norm t))).toContinuousLinearMap.comp
    (planeScalarEmbedding ell hell (columnEnvelope t))

theorem columnPlaneEmbedding_coe (ell : ℝ) (hell : 0 < ell) (t : ℂ →ᵇ V) (v : CountableOrbital) :
    (columnPlaneEmbedding ell hell t v : ℂ → V) =ᵐ[volume]
      fun z => inner ℂ (planeEvaluation ell z) v • t z := by
  have h := orbitalColumnIsometry_apply (μ := (volume : Measure ℂ)) _ (direction_measurable t).aestronglyMeasurable
    (Filter.Eventually.of_forall (direction_norm t)) (planeScalarEmbedding ell hell (columnEnvelope t) v)
  filter_upwards [h,planeScalarEmbedding_coe ell hell (columnEnvelope t) v] with z hz hv
  change _ = _ at hz
  rw [hv, mul_comm, ← smul_smul, columnEnvelope_factor] at hz
  exact hz

theorem columnPlaneEmbedding_gram (ell : ℝ) (hell : 0 < ell) (t : ℂ →ᵇ V) :
    gramOperator (columnPlaneEmbedding ell hell t) = planeScalarGram ell hell (columnEnvelope t) :=
  orbitalColumn_gram _ _ (direction_measurable t).aestronglyMeasurable (Filter.Eventually.of_forall (direction_norm t))

end VortexGap.Fermion

namespace VortexGap.Fermion
open MeasureTheory VortexGap.Frame
open scoped BoundedContinuousFunction ComplexOrder
variable {ι : Type*} [Fintype ι] [Nonempty ι]
local notation "V" => EuclideanSpace ℂ ι
local notation "Orb" => CountableOrbital →L[ℂ] CountableOrbital

def columnDirectionalEnergy (R : Orb) (ell : ℝ) (t : ℂ →ᵇ V) (z c : ℂ) (x : CountableSpace) :=
  ∑ i, ∑ j, ‖(((t z i) • planeFilteredField R ell z) *
    deriv (fun s : ℝ => let w := z+(s:ℂ)*c
      (t w j) • planeFilteredField R ell w) 0) x‖^2

theorem columnDirectionalEnergy_eq (R : Orb) (ell : ℝ) (t : ℂ →ᵇ V)
    (ht : ∀ i, Differentiable ℝ (fun z => t z i)) (z c : ℂ) (x : CountableSpace) :
    columnDirectionalEnergy R ell t z c x =
      ‖t z‖^4 * ‖(planeFilteredField R ell z * planeFilteredFieldDerivative R ell z c) x‖^2 := by
  let p := fun s : ℝ => z+(s:ℂ)*c
  have hp : HasDerivAt p c 0 := by simpa [p] using (Complex.ofRealCLM.hasDerivAt.mul_const c).const_add z
  have h := orbitalColumn_contact_energy (fun s => planeFilteredField R ell (p s))
    (planeFilteredField_hasDerivAt_direction R ell z c)
    (v := R (planeEvaluation ell (p 0))) rfl (fun j s => t (p s) j)
    (fun j => (ht j _).comp 0 hp.differentiableAt) x
  simpa only [columnDirectionalEnergy,p,Complex.ofReal_zero,zero_mul,add_zero,← EuclideanSpace.norm_sq_eq,
    ← pow_mul, Nat.reduceMul] using! h

def columnContactDensity (R : Orb) (ell : ℝ) (t : ℂ →ᵇ V) (z : ℂ) (N : ℕ) (x : countableSector N) :=
  4*Real.pi*ell^4*(columnDirectionalEnergy R ell t z 1 x + columnDirectionalEnergy R ell t z Complex.I x)

theorem columnContact_pair (R : Orb) (hR : 0 ≤ R) (ell : ℝ) (hell : 0 < ell) (t : ℂ →ᵇ V)
    (ht : ∀ i, Differentiable ℝ (fun z => t z i)) (z : ℂ) (N : ℕ) (x : countableSector N) :
    columnContactDensity R ell t z N x =
      ‖columnEnvelope t z‖^4 * (1/(Real.pi*ell^2)) * ‖countablePairAnnihilate N
        (countablePairFilter R hR (countableTwoFramePair
          (planeTwoFrame ((starRingEnd ℂ) (planeCoordinate ell z))))) x‖^2 := by
  rw [columnContactDensity, columnDirectionalEnergy_eq R ell t ht, columnDirectionalEnergy_eq R ell t ht]
  have he : ‖columnEnvelope t z‖ = ‖t z‖ := by change ‖((‖t z‖ : ℝ) : ℂ)‖ = _; simp
  rw [he]
  linear_combination (‖t z‖^4) * planeFilteredField_xy_energy R hR ell hell z N x

theorem columnContact_energy (R : Orb) (hR : 0 ≤ R) (ell : ℝ) (hell : 0 < ell) (t : ℂ →ᵇ V)
    (ht : ∀ i, Differentiable ℝ (fun z => t z i)) (N : ℕ) (x : countableSector N) :
    (∫ z, columnContactDensity R ell t z N x) =
      (inner ℂ x (filteredPairHamiltonian N R hR (planeWeightedPairOperator ell (columnEnvelope t)) x)).re := by
  let f := columnEnvelope t
  simp_rw [columnContact_pair R hR ell hell t ht]
  rw [planeContact_integral_weight ell hell (fun z => ‖f z‖^4)
    (fun a => ‖countablePairAnnihilate N (countablePairFilter R hR (countableTwoFramePair (planeTwoFrame a))) x‖^2)]
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

/-- Gram and projected pair bounds for the actual column determine the physical
contact above its full kernel. The reference inequality is on the original
sectors. No derivative or pointwise inverse of the column norm is used. -/
theorem orbitalColumn_physical_criterion (ell : ℝ) (hell : 0 < ell) (t : ℂ →ᵇ V)
    (ht : ∀ i, Differentiable ℝ (fun z => t z i)) (g u κ γ : ℝ) (hg : 0 < g)
    (hgu : g ≤ u) (hκ : 0 < κ)
    (hlo : g • (1:Orb) ≤ gramOperator (columnPlaneEmbedding ell hell t))
    (hhi : gramOperator (columnPlaneEmbedding ell hell t) ≤ u • (1:Orb))
    (hw : (κ:ℂ) • planePairOperator ≤ planeWeightedPairOperator ell (columnEnvelope t))
    (N : ℕ) (href : ∀ j ≤ N, let H := countablePairLift j planePairOperator
      (H*H-(γ:ℂ) • H).IsPositive) :
    let R := gramInvSqrt (columnPlaneEmbedding ell hell t)
    ∃ A : countableSector N →L[ℂ] countableSector N, A.IsPositive ∧
      (∀ x, (inner ℂ x (A x)).re = ∫ z, columnContactDensity R ell t z N x) ∧
      ∀ s ∈ spectrum ℝ A, s = 0 ∨ κ/g^2*(γ-14*(1-g/u)-(1-g/u)^2) ≤ s := by
  let F := columnPlaneEmbedding ell hell t
  let R := gramInvSqrt F
  have hG := gramOperator_strict F g hg hlo
  have hR := gramInvSqrt_nonneg F hG
  let M := (Real.sqrt g : ℂ) • R
  have hM : 0 ≤ M := smul_nonneg (show 0 ≤ (Real.sqrt g : ℂ) by exact_mod_cast Real.sqrt_nonneg g) hR
  have he : gramFilter (gramOperator F) g = M := by
    rw [gramFilter_eq_normalized_inverse]; ext v; rfl
  have hm : ‖M‖ ≤ 1 := by simpa only [he] using gramFilter_contraction (gramOperator F) g hg hlo
  have hd : ‖1-M^2‖ ≤ 1-g/u := by simpa only [he] using gramFilter_loss_le (gramOperator F) g u hg hgu hlo hhi
  have hl := plane_filtered_transfer M hM hm γ N href
  dsimp only at hl
  have heq : filteredPairHamiltonian N M hM planePairOperator = planeFilteredHamiltonian M hM N :=
    filteredPairHamiltonian_eq_continuous _ _ _ _ _ _ M hM N
  rw [← heq] at hl
  let f := columnEnvelope t
  let A := filteredPairHamiltonian N R hR (planeWeightedPairOperator ell f)
  have hA : A.IsPositive := filteredPairHamiltonian_positive _ _ _ _ (planeWeightedPairOperator_positive ell f)
  refine ⟨A,hA,fun x => (columnContact_energy R hR ell hell t ht N x).symm,?_⟩
  apply kernel_complement_gap_spectrum A (ContinuousLinearMap.nonneg_iff_isPositive.mpr hA)
  have hc := filtered_coercivity_kernel_gap N R hR planePairOperator (planeWeightedPairOperator ell f)
    (ContinuousLinearMap.nonneg_iff_isPositive.mpr planePairOperator_positive)
    κ (‖f‖^4) g (γ-14*‖1-M^2‖-‖1-M^2‖^2) hκ hg hw
    (by simpa only [Complex.ofReal_pow] using planeWeightedPairOperator_upper ell f) hl
  intro x hx
  have hdec : γ-14*(1-g/u)-(1-g/u)^2 ≤ γ-14*‖1-M^2‖-‖1-M^2‖^2 := by
    nlinarith [norm_nonneg (1-M^2)]
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdec
    (div_pos hκ (sq_pos_of_pos hg)).le) (sq_nonneg ‖x‖)).trans (hc.2 x hx)

end VortexGap.Fermion
