import VortexGap.Physical.OrbitalColumnCriterion
import VortexGap.Examples.PeriodicPhysical
import VortexGap.Examples.PlaneNodalFourier

noncomputable section

namespace VortexGap.Fermion
open MeasureTheory
open scoped BoundedContinuousFunction ComplexOrder
local notation "V" => EuclideanSpace ℂ (Fin 2)
local notation "Orb" => CountableOrbital →L[ℂ] CountableOrbital

private def crossedValue (k : ℝ) (z : ℂ) : V :=
  WithLp.toLp 2 ![(Real.cos (k*z.re) : ℂ),Complex.I * (Real.cos (k*z.im) : ℂ)]

private theorem crossed_components (k : ℝ) (j : Fin 2) :
    Differentiable ℝ (fun z => crossedValue k z j) := by
  fin_cases j <;> simp [crossedValue] <;> fun_prop

private theorem crossed_norm (k : ℝ) (z : ℂ) :
    ‖crossedValue k z‖^2 = Real.cos (k*z.re)^2 + Real.cos (k*z.im)^2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
  simp only [crossedValue,PiLp.toLp_apply, Matrix.cons_val_zero,Matrix.cons_val_one,
    norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,sq_abs]

def crossedColumn (ell : ℝ) : ℂ →ᵇ V :=
  let k := planeNodalWaveNumber ell
  BoundedContinuousFunction.ofNormedAddCommGroup (crossedValue k)
    ((PiLp.continuous_toLp 2 _).comp (continuous_pi (fun i => (crossed_components k i).continuous)))
    2 (fun z => by nlinarith [crossed_norm k z,Real.cos_sq_le_one (k*z.re),Real.cos_sq_le_one (k*z.im)])

private theorem crossed_envelope (ell : ℝ) (z : ℂ) :
    ‖columnEnvelope (crossedColumn ell) z‖ = ‖crossedValue (planeNodalWaveNumber ell) z‖ := by
  change ‖((‖crossedValue _ z‖ : ℝ):ℂ)‖ = _; simp

theorem crossed_gram (ell : ℝ) (hell : 0 < ell) :
    (1-1/500:ℝ) • (1:Orb) ≤ gramOperator (columnPlaneEmbedding ell hell (crossedColumn ell)) ∧
      gramOperator (columnPlaneEmbedding ell hell (crossedColumn ell)) ≤ (1+1/500:ℝ) • (1:Orb) := by
  let k := planeNodalWaveNumber ell
  let f := columnEnvelope (crossedColumn ell)
  let b := periodicEnvelope (1/2) (2*k) (by norm_num)
  have hs : star f*f = (2:ℂ) • (star b*b) - 1 := by
    ext1 z
    change (starRingEnd ℂ) (f z)*f z = 2*((starRingEnd ℂ) (b z)*b z)-1
    rw [Complex.conj_mul',Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_pow]
    norm_cast
    rw [show ‖f z‖ = _ from crossed_envelope ell z,crossed_norm,show ‖b z‖^2 = _ from periodicEnvelope_norm_sq (by norm_num) (by norm_num) _ z]
    unfold periodicWeight
    rw [mul_assoc 2 k z.re,mul_assoc 2 k z.im,Real.cos_two_mul,Real.cos_two_mul]
    ring
  rw [columnPlaneEmbedding_gram]
  apply planeGram_bounds_of_deviation ell hell f 1 (1/500)
  have he : planeToeplitzMap ell hell (star f*f) - (1:ℂ) • (1:Orb) =
      (2:ℂ) • (planeToeplitzMap ell hell (star b*b) - (1:ℂ) • (1:Orb)) := by
    rw [hs,map_sub,map_smul,planeToeplitzMap_one]
    ext1 x
    simp only [smul_apply,sub_apply,one_apply_eq_self,one_smul]
    module
  rw [Complex.ofReal_one,he,norm_smul]
  have hh := periodicEnvelope_gram_deviation ell hell (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num) (2*k)
  change ‖planeToeplitzMap ell hell (star b*b) - _‖ ≤ _ at hh
  have hk : k^2*ell^2 = 2*Real.pi := by
    dsimp [k,planeNodalWaveNumber]; rw [div_pow,Real.sq_sqrt (by positivity)]; field_simp
  have he' : -(2*k)^2*ell^2/4 = -(2*Real.pi) := by nlinarith [hk]
  rw [he'] at hh
  norm_num only [Complex.norm_ofNat]
  linarith [planeNodal_exp_bounds.2]

theorem crossed_weight_comparison (ell : ℝ) (z : ℂ) :
    ‖planeNodal ell z‖^4 / 4 ≤ ‖columnEnvelope (crossedColumn ell) z‖^4 := by
  let k := planeNodalWaveNumber ell
  let a := Real.cos (k*z.re)
  let b := Real.cos (k*z.im)
  have ha : a^2 ≤ 1 := Real.cos_sq_le_one _
  have hb : b^2 ≤ 1 := Real.cos_sq_le_one _
  have h : 2*a^2*b^2 ≤ a^2+b^2 := by
    nlinarith [mul_nonneg (sq_nonneg a) (sub_nonneg.mpr hb),mul_nonneg (sq_nonneg b) (sub_nonneg.mpr ha)]
  have hn : ‖planeNodal ell z‖^4 = (2*a*b)^4 := by
    change ‖((2*a*b : ℝ):ℂ)‖^4 = _
    rw [Complex.norm_real,Real.norm_eq_abs,show (4:ℕ)=2*2 by decide,pow_mul,sq_abs]; ring
  rw [hn,crossed_envelope,show (4:ℕ)=2*2 by decide,pow_mul (‖crossedValue _ z‖),crossed_norm]
  change _ ≤ (a^2+b^2)^2
  nlinarith [pow_le_pow_left₀ (by positivity) h 2]

theorem crossed_pair_lower (ell : ℝ) (hell : 0 < ell) :
    (0.49539:ℂ) • planePairOperator ≤ planeWeightedPairOperator ell (columnEnvelope (crossedColumn ell)) := by
  let f := columnEnvelope (crossedColumn ell)
  let B := planeWeightedPairOperator ell (planeNodal ell)
  have hB : B.IsPositive := planeWeightedPairOperator_positive ..
  have hc : 0 ≤ ((1/4:ℝ):ℂ) := by exact_mod_cast (by norm_num : (0:ℝ) ≤ 1/4)
  have hlow := smul_le_smul_of_nonneg_left (planeNodal_pair_lower ell hell) hc
  rw [smul_smul] at hlow
  have hconst : ((1/4:ℝ):ℂ) * 1.98156 = 0.49539 := by norm_num
  rw [hconst] at hlow
  apply hlow.trans
  apply positive_operator_le_of_energy _ _ (ContinuousLinearMap.nonneg_iff_isPositive.mp
    (smul_nonneg hc (ContinuousLinearMap.nonneg_iff_isPositive.mpr hB))) (planeWeightedPairOperator_positive ell f)
  intro q
  simp only [smul_apply,inner_smul_right,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  rw [planeWeightedPairOperator_energy,planeWeightedPairOperator_energy,← integral_const_mul]
  have integrableWeight (g : ℂ →ᵇ ℂ) : MeasureTheory.Integrable
      (fun a => ‖g ((Real.sqrt 2*ell : ℝ) • (starRingEnd ℂ) a)‖^4 *
        ‖inner ℂ (countableTwoFramePair (planeTwoFrame a)) q‖^2) planePairMeasure := by
    have hg := planeWeightedPair_coefficient_memLp ell g q
    have hi := (MeasureTheory.memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg
    simpa only [planeWeightedPair_coefficient_norm,mul_pow,planeContactWeightRoot_norm,← pow_mul] using hi
  apply MeasureTheory.integral_mono ((integrableWeight _).const_mul _) (integrableWeight f)
  intro x
  have hx := crossed_weight_comparison ell ((Real.sqrt 2*ell:ℝ) • (starRingEnd ℂ) x)
  dsimp only
  rw [← mul_assoc]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  linarith

theorem crossed_physical_gap (ell : ℝ) (hell : 0 < ell) (N : ℕ)
    (href : ∀ j ≤ N, let H := countablePairLift j planePairOperator
      (H*H-(1/5:ℂ) • H).IsPositive) :
    let R := gramInvSqrt (columnPlaneEmbedding ell hell (crossedColumn ell))
    ∃ A : countableSector N →L[ℂ] countableSector N, A.IsPositive ∧
      (∀ x, (inner ℂ x (A x)).re = ∫ z, columnContactDensity R ell (crossedColumn ell) z N x) ∧
      ∀ s ∈ spectrum ℝ A, s = 0 ∨ (0.0716:ℝ) < s := by
  obtain ⟨A,hA,he,hg⟩ := orbitalColumn_physical_criterion ell hell (crossedColumn ell)
    (crossed_components _) (1-1/500) (1+1/500) 0.49539 (1/5) (by norm_num) (by norm_num) (by norm_num)
    (crossed_gram ell hell).1 (crossed_gram ell hell).2 (by convert crossed_pair_lower ell hell using 1)
    N (by simpa using href)
  exact ⟨A,hA,he,fun s hs => (hg s hs).imp_right fun hh => lt_of_lt_of_le (by norm_num) hh⟩

theorem crossed_zero_iff (ell : ℝ) (z : ℂ) :
    crossedColumn ell z = 0 ↔ Real.cos (planeNodalWaveNumber ell*z.re) = 0 ∧
      Real.cos (planeNodalWaveNumber ell*z.im) = 0 := by
  rw [← norm_eq_zero]
  change ‖crossedValue (planeNodalWaveNumber ell) z‖ = 0 ↔ _
  have h := crossed_norm (planeNodalWaveNumber ell) z
  constructor
  · intro hz
    rw [hz] at h
    constructor <;> nlinarith [sq_nonneg (Real.cos (planeNodalWaveNumber ell*z.re)),
      sq_nonneg (Real.cos (planeNodalWaveNumber ell*z.im))]
  · rintro ⟨hx,hy⟩
    rw [hx,hy] at h
    nlinarith

theorem crossed_has_node (ell : ℝ) (hell : 0 < ell) :
    ∃ z : ℂ, crossedColumn ell z = 0 := by
  let k := planeNodalWaveNumber ell
  have hk : k ≠ 0 := by dsimp [k,planeNodalWaveNumber]; positivity
  let x := Real.pi / (2*k)
  have he : k*x = Real.pi/2 := by dsimp [x]; field_simp
  refine ⟨⟨x,x⟩,(crossed_zero_iff ell _).mpr ?_⟩
  change Real.cos (k*x) = 0 ∧ Real.cos (k*x) = 0
  simp [he,Real.cos_pi_div_two]

end VortexGap.Fermion
