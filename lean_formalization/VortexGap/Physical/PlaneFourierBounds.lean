import VortexGap.Physical.PlanePairFourier
import VortexGap.Physical.PlaneGramDomain
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory
open scoped InnerProduct ComplexOrder BoundedContinuousFunction
local notation "Orb" => CountableOrbital →L[ℂ] CountableOrbital
local notation "H" => Lp ℂ 2 (volume : Measure ℂ)

private theorem scalarEmbedding_bound (ell : ℝ) (hell : 0 < ell) (a : ℂ →ᵇ ℂ) :
    ‖planeScalarEmbedding ell hell a‖ ≤ ‖a‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow, Frame.l2_norm_sq_integral]
  apply le_trans (le_of_eq (integral_congr_ae ?_)) (planeScalar_coefficient_bound ell hell a v)
  filter_upwards [planeScalarEmbedding_coe ell hell a v] with z hz
  rw [hz]

private def symbolLinear (ell : ℝ) (hell : 0 < ell) : (ℂ →ᵇ ℂ) →ₗ[ℂ] Orb where
  toFun := planeToeplitz ell hell
  map_add' a b := by
    ext1 v
    have he : planeScalarEmbedding ell hell (a+b) v =
        planeScalarEmbedding ell hell a v + planeScalarEmbedding ell hell b v := by
      apply Lp.ext
      filter_upwards [planeScalarEmbedding_coe ell hell (a+b) v, planeScalarEmbedding_coe ell hell a v,
        planeScalarEmbedding_coe ell hell b v, Lp.coeFn_add (planeScalarEmbedding ell hell a v)
          (planeScalarEmbedding ell hell b v)] with z ht ha hb hs
      simp only [ht,hs,Pi.add_apply,ha,hb,BoundedContinuousFunction.add_apply,add_mul]
    simp only [planeToeplitz,ContinuousLinearMap.comp_apply,he,map_add,add_apply]
  map_smul' c a := by
    ext1 v
    have he : planeScalarEmbedding ell hell (c • a) v = c • planeScalarEmbedding ell hell a v := by
      apply Lp.ext
      filter_upwards [planeScalarEmbedding_coe ell hell (c • a) v, planeScalarEmbedding_coe ell hell a v,
        Lp.coeFn_smul c (planeScalarEmbedding ell hell a v)] with z ht ha hs
      simp only [ht,hs,Pi.smul_apply,ha,BoundedContinuousFunction.smul_apply, smul_eq_mul,mul_assoc]
    change _ = (c • planeToeplitz ell hell a) v
    simp only [planeToeplitz,ContinuousLinearMap.comp_apply,he,map_smul,smul_apply]

def planeToeplitzMap (ell : ℝ) (hell : 0 < ell) : (ℂ →ᵇ ℂ) →L[ℂ] Orb :=
  (symbolLinear ell hell).mkContinuous 1 (fun a => by
    rw [one_mul]
    let J := planeLLLEmbedding ell hell
    have hJ : ‖J.toContinuousLinearMap.adjoint‖ ≤ 1 := by
      rw [ContinuousLinearMap.adjoint.norm_map]
      exact J.norm_toContinuousLinearMap_le
    change ‖J.toContinuousLinearMap.adjoint.comp (planeScalarEmbedding ell hell a)‖ ≤ _
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul hJ (scalarEmbedding_bound ell hell a) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)))

theorem planeToeplitzMap_one (ell : ℝ) (hell : 0 < ell) :
    planeToeplitzMap ell hell 1 = 1 := by
  let J := planeLLLEmbedding ell hell
  have he : planeScalarEmbedding ell hell 1 = J.toContinuousLinearMap := by
    ext1 v
    apply Lp.ext
    filter_upwards [planeScalarEmbedding_coe ell hell 1 v, planeLLLEmbedding_coe ell hell v] with z ha hb
    change planeScalarEmbedding ell hell 1 v z = planeLLLEmbedding ell hell v z
    rw [ha,hb]
    exact one_mul _
  change J.toContinuousLinearMap.adjoint.comp (planeScalarEmbedding ell hell 1) = 1
  rw [he]
  exact (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mp J.norm_map

theorem planeToeplitzMap_fourier (ell : ℝ) (hell : 0 < ell) (q : ℂ) :
    planeToeplitzMap ell hell (planeFourierPhase q) =
      (Real.exp (-‖q‖^2*ell^2/4) : ℂ) • (planeGuidingTranslation ell hell q).toLinearIsometry.toContinuousLinearMap :=
  planeFourier_compression ell hell q

theorem planeFourier_mode_norm (ell : ℝ) (hell : 0 < ell) (q : ℂ) :
    ‖planeToeplitzMap ell hell (planeFourierPhase q)‖ ≤ Real.exp (-‖q‖^2*ell^2/4) := by
  rw [planeToeplitzMap_fourier,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact mul_le_of_le_one_right (Real.exp_pos _).le (planeGuidingTranslation ell hell q).toLinearIsometry.norm_toContinuousLinearMap_le

private theorem fourierPhase_norm_le (q : ℂ) : ‖planeFourierPhase q‖ ≤ 1 := by
  apply (BoundedContinuousFunction.norm_le zero_le_one).mpr
  intro z
  change ‖Complex.exp _‖ ≤ 1
  simp [Complex.norm_exp]

/-- Absolute summability of scalar coefficients upgrades a pointwise Fourier
expansion to convergence in the uniform norm. -/
theorem planeFourier_uniform {ι : Type*} (a : ℂ →ᵇ ℂ) (m : ℂ) (c q : ι → ℂ)
    (hc : Summable (fun i => ‖c i‖)) (ha : ∀ z, HasSum (fun i => c i * planeFourierPhase (q i) z) (a z-m)) :
    HasSum (fun i => c i • planeFourierPhase (q i)) (a-m • 1) := by
  have hs : Summable (fun i => c i • planeFourierPhase (q i)) :=
    Summable.of_norm_bounded hc fun i => by
      rw [norm_smul]
      exact mul_le_of_le_one_right (norm_nonneg _) (fourierPhase_norm_le _)
  convert hs.hasSum using 1
  ext1 z
  let ev : (ℂ →ᵇ ℂ) →+ ℂ := ⟨⟨fun b => b z,rfl⟩, fun _ _ => rfl⟩
  have h := hs.hasSum.map ev (continuous_eval_const z)
  change HasSum (fun i => c i * planeFourierPhase (q i) z) _ at h
  change a z - m * 1 = _
  rw [mul_one]
  exact (ha z).unique h

/-- Operator-norm tail after any finite set of nonconstant modes. The
right side keeps the Gaussian attenuation of every omitted term. -/
theorem planeFourier_tail {ι : Type*} (ell : ℝ) (hell : 0 < ell) (a : ℂ →ᵇ ℂ) (m : ℂ)
    (c q : ι → ℂ) (hc : Summable (fun i => ‖c i‖))
    (ha : ∀ z, HasSum (fun i => c i * planeFourierPhase (q i) z) (a z-m)) (s : Finset ι) :
    ‖planeToeplitzMap ell hell a - m • (1 : Orb) -
      ∑ i ∈ s, c i • planeToeplitzMap ell hell (planeFourierPhase (q i))‖ ≤
      ∑' i : {j // j ∉ s}, ‖c i.val‖ * Real.exp (-‖q i.val‖^2*ell^2/4) := by
  classical
  let T := planeToeplitzMap ell hell
  let op := fun i => c i • T (planeFourierPhase (q i))
  let b := fun i => ‖c i‖ * Real.exp (-‖q i‖^2*ell^2/4)
  have hb (i) : ‖op i‖ ≤ b i := by
    rw [show ‖op i‖ = ‖c i‖ * ‖T (planeFourierPhase (q i))‖ from norm_smul _ _]
    exact mul_le_mul_of_nonneg_left (planeFourier_mode_norm ell hell _) (norm_nonneg _)
  have hsum : Summable b := Summable.of_nonneg_of_le (fun i => by dsimp [b]; positivity) (fun i =>
    mul_le_of_le_one_right (norm_nonneg _) (Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (sq_nonneg _)) (by norm_num)))) hc
  have hnorm : Summable (fun i => ‖op i‖) := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hsum
  have h := (planeFourier_uniform a m c q hc ha).map T.toAddMonoidHom T.continuous
  change HasSum (fun i => T (c i • planeFourierPhase (q i))) (T (a-m • 1)) at h
  simp only [map_smul,map_sub,T,planeToeplitzMap_one] at h
  change HasSum op (T a - m • 1) at h
  have he := h.summable.sum_add_tsum_subtype_compl s
  rw [h.tsum_eq] at he
  change ‖T a-m • 1 - ∑ i ∈ s, op i‖ ≤ _
  rw [← he, add_sub_cancel_left]
  exact (norm_tsum_le_tsum_norm (hnorm.subtype _)).trans
    ((hnorm.subtype _).tsum_le_tsum (fun j => hb j.val) (hsum.subtype _))

theorem planeFourier_finite_bound {ι : Type*} (ell : ℝ) (hell : 0 < ell) (a : ℂ →ᵇ ℂ)
    (m : ℂ) (s : Finset ι) (c q : ι → ℂ)
    (ha : ∀ z, a z = m + ∑ i ∈ s, c i * planeFourierPhase (q i) z) :
    ‖planeToeplitzMap ell hell a - m • (1 : Orb)‖ ≤ ∑ i ∈ s, ‖c i‖ * Real.exp (-‖q i‖^2*ell^2/4) := by
  have he : a = m • 1 + ∑ i ∈ s, c i • planeFourierPhase (q i) := by
    ext1 z
    simpa [BoundedContinuousFunction.add_apply, BoundedContinuousFunction.sum_apply,
      BoundedContinuousFunction.smul_apply] using ha z
  rw [he,map_add,map_smul,planeToeplitzMap_one,add_sub_cancel_left,map_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [map_smul,norm_smul]
  exact mul_le_mul_of_nonneg_left (planeFourier_mode_norm ell hell _) (norm_nonneg _)

theorem planeScalarGram_toeplitz (ell : ℝ) (hell : 0 < ell) (f : ℂ →ᵇ ℂ) :
    planeScalarGram ell hell f = planeToeplitzMap ell hell (star f*f) := by
  ext1 v
  exact planeScalarGram_compression ell hell f v

private theorem centered_energy (A : Orb) (m e : ℝ) (h : ‖A-(m : ℂ) • 1‖ ≤ e) (v : CountableOrbital) :
    (m-e)*‖v‖^2 ≤ (inner ℂ v (A v)).re ∧ (inner ℂ v (A v)).re ≤ (m+e)*‖v‖^2 := by
  let D := A - (m : ℂ) • 1
  have hb : ‖inner ℂ v (D v)‖ ≤ e*‖v‖^2 := by
    calc
      _ ≤ ‖v‖*‖D v‖ := norm_inner_le_norm _ _
      _ ≤ ‖v‖*(e*‖v‖) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        exact (D.le_opNorm v).trans (mul_le_mul_of_nonneg_right h (norm_nonneg _))
      _ = _ := by ring
  have hh : |(inner ℂ v (A v)).re - m*‖v‖^2| ≤ e*‖v‖^2 := by
    have ht := (Complex.abs_re_le_norm (inner ℂ v (D v))).trans hb
    change |(inner ℂ v (A v - (m : ℂ) • v)).re| ≤ _ at ht
    have hre : (inner ℂ v v).re = ‖v‖^2 := by
      simpa only [RCLike.re_eq_complex_re] using! (norm_sq_eq_re_inner (𝕜 := ℂ) v).symm
    simpa only [inner_sub_right,inner_smul_right,Complex.sub_re,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,sub_zero,hre] using ht
  obtain ⟨hl,hu⟩ := abs_le.mp hh
  constructor <;> linarith

private theorem centered_order {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (A : E →L[ℂ] E) (hA : 0 ≤ A) (m e : ℝ)
    (h : ‖A-m • 1‖ ≤ e) :
    (m-e) • (1 : E →L[ℂ] E) ≤ A ∧ A ≤ (m+e) • 1 := by
  let D := A-m • 1
  have hma : IsSelfAdjoint (algebraMap ℝ (E →L[ℂ] E) m) :=
    IsSelfAdjoint.algebraMap (E →L[ℂ] E) (.all m)
  rw [Algebra.algebraMap_eq_smul_one] at hma
  have hD : IsSelfAdjoint D := (IsSelfAdjoint.of_nonneg hA).sub hma
  have ht := hD.le_algebraMap_norm_self
  have hb := hD.neg_algebraMap_norm_le_self
  rw [Algebra.algebraMap_eq_smul_one] at ht hb
  have he : ‖D‖ • (1 : E →L[ℂ] E) ≤ e • (1 : E →L[ℂ] E) := smul_le_smul_of_nonneg_right h zero_le_one
  have hu := ht.trans he
  have hl := (neg_le_neg he).trans hb
  change - (e • (1 : E →L[ℂ] E)) ≤ A - m • 1 at hl
  change A - m • (1 : E →L[ℂ] E) ≤ e • 1 at hu
  change _ ≤ A ∧ A ≤ _
  rw [sub_smul, add_smul]
  exact ⟨by simpa only [sub_eq_add_neg, add_comm] using (le_sub_iff_add_le.mp hl),
    by simpa only [add_comm] using (sub_le_iff_le_add.mp hu)⟩

theorem planeGram_bounds_of_deviation (ell : ℝ) (hell : 0 < ell) (f : ℂ →ᵇ ℂ) (m e : ℝ)
    (h : ‖planeToeplitzMap ell hell (star f*f) - (m : ℂ) • 1‖ ≤ e) :
    (m-e) • (1 : Orb) ≤ planeScalarGram ell hell f ∧
      planeScalarGram ell hell f ≤ (m+e) • (1 : Orb) := by
  rw [← planeScalarGram_toeplitz] at h
  apply centered_order _ (gramOperator_nonneg _) m e
  exact h
theorem planePair_bounds_of_deviation (ell : ℝ) (hell : 0 < ell) (f : ℂ →ᵇ ℂ) (m e : ℝ)
    (hl : 0 ≤ m-e) (hu : 0 ≤ m+e)
    (h : ‖planeToeplitzMap (ell/Real.sqrt 2) (by positivity) ((star f*f)^2) - (m : ℂ) • 1‖ ≤ e) :
    ((m-e : ℝ) : ℂ) • planePairOperator ≤ planeWeightedPairOperator ell f ∧
      planeWeightedPairOperator ell f ≤ ((m+e : ℝ) : ℂ) • planePairOperator := by
  have hp (c : ℝ) (hc : 0 ≤ c) : ((c : ℂ) • planePairOperator).IsPositive :=
    ContinuousLinearMap.nonneg_iff_isPositive.mp (smul_nonneg
      (show 0 ≤ (c : ℂ) by exact_mod_cast hc)
      (ContinuousLinearMap.nonneg_iff_isPositive.mpr planePairOperator_positive))
  have henergy (p : CountablePairSpace) := centered_energy _ m e h (planePairRightCoordinates (star p))
  have he (c : ℝ) (p : CountablePairSpace) :
      (inner ℂ p (((c : ℂ) • planePairOperator) p)).re = c * ‖planePairRightCoordinates (star p)‖^2 := by
    rw [smul_apply,inner_smul_right,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
      ← planePairOperator_energy_star,planePairOperator_energy]
  constructor
  · apply positive_operator_le_of_energy _ _ (hp _ hl) (planeWeightedPairOperator_positive ell f)
    intro p
    rw [he, planeWeightedPair_center_energy ell hell]
    exact (henergy p).1
  · apply positive_operator_le_of_energy _ _ (planeWeightedPairOperator_positive ell f) (hp _ hu)
    intro p
    rw [he, planeWeightedPair_center_energy ell hell]
    exact (henergy p).2

end VortexGap.Fermion
