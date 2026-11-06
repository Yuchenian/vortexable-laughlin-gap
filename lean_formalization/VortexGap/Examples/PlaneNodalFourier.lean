import VortexGap.Physical.PlaneFourierBounds
import VortexGap.Examples.PlaneBandDistinct
import Mathlib.Analysis.Real.Pi.Bounds
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory
open scoped ComplexOrder BoundedContinuousFunction

def planeNodalWaveNumber (ell : ℝ) := Real.sqrt (2*Real.pi)/ell

def planeNodal (ell : ℝ) : ℂ →ᵇ ℂ :=
  let k := planeNodalWaveNumber ell
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun z => ((2*Real.cos (k*z.re)*Real.cos (k*z.im) : ℝ) : ℂ))
    (by fun_prop) 2 (fun z => by
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2)]
      nlinarith [abs_nonneg (Real.cos (k*z.re)), abs_nonneg (Real.cos (k*z.im)),
        mul_le_mul (abs_le.mpr ⟨Real.neg_one_le_cos _,Real.cos_le_one _⟩ :
          |Real.cos (k*z.re)| ≤ 1) (abs_le.mpr ⟨Real.neg_one_le_cos _,Real.cos_le_one _⟩ :
          |Real.cos (k*z.im)| ≤ 1) (abs_nonneg _) zero_le_one])

theorem planeNodal_differentiable (ell : ℝ) : Differentiable ℝ (planeNodal ell) := by
  change Differentiable ℝ (fun z : ℂ => ((2*Real.cos (planeNodalWaveNumber ell*z.re)*
    Real.cos (planeNodalWaveNumber ell*z.im) : ℝ) : ℂ))
  fun_prop

theorem planeNodal_has_zero (ell : ℝ) (hell : 0 < ell) :
    planeNodal ell ((Real.pi/(2*planeNodalWaveNumber ell) : ℝ) : ℂ) = 0 := by
  let k := planeNodalWaveNumber ell
  have hk : k ≠ 0 := by dsimp [k,planeNodalWaveNumber]; positivity
  change ((2*Real.cos (k*((Real.pi/(2*k) : ℝ) : ℂ).re)*
    Real.cos (k*((Real.pi/(2*k) : ℝ) : ℂ).im) : ℝ) : ℂ) = 0
  simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, Real.cos_zero, mul_one]
  rw [show k*(Real.pi/(2*k)) = Real.pi/2 by field_simp, Real.cos_pi_div_two]
  simp

private def axisCoeff (m j : ℕ) : ℝ := ((2*m).choose j : ℝ)/(2:ℝ)^m
private def axisFreq (k : ℝ) (m j : ℕ) := 2*k*((j:ℝ)-m)
private def nodalFreq (k : ℝ) (m : ℕ) (i : ℕ × ℕ) : ℂ := ⟨axisFreq k m i.1, axisFreq k m i.2⟩
private def squareModes (m : ℕ) := (Finset.range (2*m+1)) ×ˢ (Finset.range (2*m+1))

private theorem axis_expansion (m : ℕ) (k t : ℝ) :
    (2 : ℂ)^m * (Real.cos (k*t) : ℂ)^(2*m) =
      ∑ j ∈ Finset.range (2*m+1), (axisCoeff m j : ℂ) *
        Complex.exp (Complex.I * ((axisFreq k m j*t : ℝ) : ℂ)) := by
  let x := ((k*t : ℝ) : ℂ)*Complex.I
  have he : (2 : ℂ) * (Real.cos (k*t) : ℂ) = Complex.exp x + Complex.exp (-x) := by
    rw [Complex.ofReal_cos,Complex.cos]
    simp only [neg_mul,x]
    ring
  have hn : (2 : ℂ)^m ≠ 0 := pow_ne_zero _ (by norm_num)
  apply (mul_right_cancel₀ hn)
  rw [Finset.sum_mul]
  calc
    _ = ((2:ℂ) * (Real.cos (k*t) : ℂ))^(2*m) := by rw [mul_pow,show 2*m=m+m by omega,pow_add]; ring
    _ = _ := by
      rw [he, add_pow]
      apply Finset.sum_congr rfl
      intro j hj
      have hj' : j ≤ 2*m := by simpa using Finset.mem_range.mp hj
      rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
      have hfreq : (j:ℂ)*x + ((2*m-j : ℕ):ℂ)*(-x) = Complex.I * ((axisFreq k m j*t : ℝ) : ℂ) := by
        simp only [x,axisFreq,Nat.cast_sub hj',Nat.cast_mul,Nat.cast_ofNat,
          Complex.ofReal_mul,Complex.ofReal_sub,Complex.ofReal_natCast, Complex.ofReal_ofNat]
        ring
      rw [hfreq]
      simp only [axisCoeff,Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_ofNat,Complex.ofReal_natCast]
      field_simp

private theorem nodal_expansion (ell : ℝ) (m : ℕ) (z : ℂ) :
    (planeNodal ell z)^(2*m) =
      ∑ i ∈ squareModes m, ((axisCoeff m i.1 * axisCoeff m i.2 : ℝ) : ℂ) *
        planeFourierPhase (nodalFreq (planeNodalWaveNumber ell) m i) z := by
  let k := planeNodalWaveNumber ell
  change ((2*Real.cos (k*z.re)*Real.cos (k*z.im) : ℝ) : ℂ)^(2*m) = _
  rw [show ((2*Real.cos (k*z.re)*Real.cos (k*z.im) : ℝ) : ℂ)^(2*m) =
    ((2:ℂ)^m*(Real.cos (k*z.re):ℂ)^(2*m))*((2:ℂ)^m*(Real.cos (k*z.im):ℂ)^(2*m)) by
      push_cast; rw [show 2*m=m+m by omega]; simp only [mul_pow,pow_add]; ring]
  rw [axis_expansion,axis_expansion,Finset.sum_mul_sum, squareModes,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  change _ = _ * Complex.exp (Complex.I * ((axisFreq k m j*z.re + axisFreq k m l*z.im : ℝ) : ℂ))
  simp only [Complex.ofReal_add,mul_add,Complex.exp_add,Complex.ofReal_mul]
  ring

private def damp (b : ℝ) (m j : ℕ) := Real.exp (-b*((j:ℝ)-m)^2)

private theorem nodal_deviation (ell L : ℝ) (hL : 0 < L) (m : ℕ) :
    ‖planeToeplitzMap L hL ((star (planeNodal ell)*planeNodal ell)^m) -
        (((axisCoeff m m)^2 : ℝ) : ℂ) • (1 : CountableOrbital →L[ℂ] CountableOrbital)‖ ≤
      (∑ j ∈ Finset.range (2*m+1), axisCoeff m j * damp ((planeNodalWaveNumber ell)^2*L^2) m j)^2 -
        (axisCoeff m m)^2 := by
  let k := planeNodalWaveNumber ell
  let S := squareModes m
  let c := fun i : ℕ × ℕ => ((axisCoeff m i.1 * axisCoeff m i.2 : ℝ) : ℂ)
  let q := nodalFreq k m
  let o : ℕ × ℕ := (m,m)
  have ho : o ∈ S := by simp [o,S,squareModes]; omega
  have hz : q o = 0 := by apply Complex.ext <;> simp [q,o,nodalFreq,axisFreq]
  have hphase (z : ℂ) : planeFourierPhase 0 z = 1 := by
    change Complex.exp (Complex.I * (((0:ℂ).re*z.re + (0:ℂ).im*z.im : ℝ) : ℂ)) = 1
    simp
  have hcen : c o = (((axisCoeff m m)^2 : ℝ) : ℂ) := by simp [c,o,pow_two]
  have he (z : ℂ) : ((star (planeNodal ell)*planeNodal ell)^m) z =
      (((axisCoeff m m)^2 : ℝ) : ℂ) + ∑ i ∈ S.erase o, c i * planeFourierPhase (q i) z := by
    have hstar : star (planeNodal ell z) = planeNodal ell z := Complex.conj_ofReal _
    change (star (planeNodal ell z) * planeNodal ell z)^m = _
    rw [hstar,← sq,← pow_mul,nodal_expansion]
    change (∑ i ∈ S, c i * planeFourierPhase (q i) z) = _
    rw [← Finset.add_sum_erase S _ ho,hz,hphase,mul_one,hcen]
  apply (planeFourier_finite_bound L hL _ _ _ c q he).trans
  let b := k^2*L^2
  let a := fun j => axisCoeff m j * damp b m j
  have hc (j) : 0 ≤ axisCoeff m j := by unfold axisCoeff; positivity
  have term (i : ℕ × ℕ) : ‖c i‖ * Real.exp (-‖q i‖^2*L^2/4) = a i.1*a i.2 := by
    have hfreq : -‖q i‖^2*L^2/4 = -b*((i.1:ℝ)-m)^2 + -b*((i.2:ℝ)-m)^2 := by
      simp only [q,nodalFreq,Complex.sq_norm,Complex.normSq_apply,axisFreq,b]
      ring
    rw [hfreq,Real.exp_add]
    simp only [c,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hc _) (hc _)),a,damp]
    ring
  simp_rw [term]
  have hc0 : a m = axisCoeff m m := by simp [a,damp]
  have hfull : (∑ i ∈ S, a i.1*a i.2) = (∑ j ∈ Finset.range (2*m+1), a j)^2 := by
    dsimp only [S,squareModes]
    rw [sq, Finset.sum_mul_sum, Finset.sum_product]
  rw [← hfull, ← Finset.add_sum_erase S _ ho]
  simp [o,hc0,pow_two]

theorem planeNodal_exp_bounds :
    Real.exp (-Real.pi) < 1/23 ∧ Real.exp (-(2*Real.pi)) < 1/500 := by
  have hp : (23:ℝ) < Real.exp Real.pi := by
    calc
      _ < ∑ i ∈ Finset.range 13, (3.14 : ℝ)^i / i.factorial := by norm_num [Finset.sum_range_succ,Nat.factorial]
      _ ≤ Real.exp 3.14 := Real.sum_le_exp_of_nonneg (by norm_num) _
      _ ≤ Real.exp Real.pi := Real.exp_le_exp.mpr (by linarith [Real.pi_gt_d2])
  have h2 : (500:ℝ) < Real.exp (2*Real.pi) := by
    rw [two_mul,Real.exp_add]
    nlinarith [mul_self_lt_mul_self (by norm_num : (0:ℝ)≤23) hp]
  rw [Real.exp_neg, Real.exp_neg, inv_eq_one_div, inv_eq_one_div]
  exact ⟨one_div_lt_one_div_of_lt (by norm_num) hp,one_div_lt_one_div_of_lt (by norm_num) h2⟩

private theorem nodal_scale (ell : ℝ) (hell : 0 < ell) :
    (planeNodalWaveNumber ell)^2 * ell^2 = 2*Real.pi := by
  rw [planeNodalWaveNumber,div_pow,Real.sq_sqrt (by positivity)]
  field_simp

private theorem axis_one (b : ℝ) :
    (∑ j ∈ Finset.range 3, axisCoeff 1 j * damp b 1 j) = 1 + Real.exp (-b) := by
  norm_num [Finset.sum_range_succ,axisCoeff,damp,Nat.choose]
  ring

private theorem axis_two (b : ℝ) :
    (∑ j ∈ Finset.range 5, axisCoeff 2 j * damp b 2 j) =
      3/2 + 2*Real.exp (-b) + Real.exp (-b)^4/2 := by
  norm_num [Finset.sum_range_succ,axisCoeff,damp,Nat.choose]
  rw [← Real.exp_nat_mul]
  norm_num
  ring_nf

/-- Gram deviation for a multiplier with actual zeros. -/
theorem planeNodal_gram_deviation (ell : ℝ) (hell : 0 < ell) :
    ‖planeToeplitzMap ell hell (star (planeNodal ell)*planeNodal ell) -
      (1 : CountableOrbital →L[ℂ] CountableOrbital)‖ ≤ 0.004004 := by
  have h := nodal_deviation ell ell hell 1
  rw [nodal_scale ell hell, axis_one] at h
  norm_num [axisCoeff,Nat.choose] at h
  apply h.trans
  have he := planeNodal_exp_bounds.2
  nlinarith [sq_lt_sq' (by linarith [Real.exp_pos (-(2*Real.pi))] :
    -(1/500:ℝ) < Real.exp (-(2*Real.pi))) he]

def planeNodalPairError : ℝ := (3/2+2/23+1/(2*23^4))^2 - 9/4

theorem planeNodal_pair_deviation (ell : ℝ) (hell : 0 < ell) :
    ‖planeToeplitzMap (ell/Real.sqrt 2) (by positivity) ((star (planeNodal ell)*planeNodal ell)^2) -
      ((9/4:ℝ) : ℂ) • (1 : CountableOrbital →L[ℂ] CountableOrbital)‖ ≤ planeNodalPairError := by
  have h := nodal_deviation ell (ell/Real.sqrt 2) (by positivity) 2
  have hs : (planeNodalWaveNumber ell)^2*(ell/Real.sqrt 2)^2 = Real.pi := by
    rw [div_pow,Real.sq_sqrt (by norm_num)]
    nlinarith [nodal_scale ell hell]
  rw [hs,axis_two] at h
  norm_num [axisCoeff,Nat.choose] at h ⊢
  apply h.trans
  have he := planeNodal_exp_bounds.1.le
  have h4 := pow_le_pow_left₀ (Real.exp_pos _).le he 4
  unfold planeNodalPairError
  apply sub_le_sub_right
  apply pow_le_pow_left₀ (by positivity)
  linarith

theorem planeNodal_gram_bounds (ell : ℝ) (hell : 0 < ell) :
    (1-0.004004 : ℝ) • (1 : CountableOrbital →L[ℂ] CountableOrbital) ≤ planeScalarGram ell hell (planeNodal ell) ∧
    planeScalarGram ell hell (planeNodal ell) ≤ (1+0.004004 : ℝ) • (1 : CountableOrbital →L[ℂ] CountableOrbital) :=
  planeGram_bounds_of_deviation ell hell _ 1 0.004004 (by simpa using planeNodal_gram_deviation ell hell)

theorem planeNodal_pair_lower (ell : ℝ) (hell : 0 < ell) :
    (1.98156 : ℂ) • planePairOperator ≤ planeWeightedPairOperator ell (planeNodal ell) := by
  have h := (planePair_bounds_of_deviation ell hell _ (9/4) planeNodalPairError (by norm_num [planeNodalPairError])
    (by norm_num [planeNodalPairError]) (planeNodal_pair_deviation ell hell)).1
  apply le_trans _ h
  apply smul_le_smul_of_nonneg_right _ (ContinuousLinearMap.nonneg_iff_isPositive.mpr planePairOperator_positive)
  norm_num [planeNodalPairError,Complex.le_def]

theorem planeNodal_gram_strict (ell : ℝ) (hell : 0 < ell) :
    IsStrictlyPositive (planeScalarGram ell hell (planeNodal ell)) :=
  gramOperator_strict _ (1-0.004004) (by norm_num) (planeNodal_gram_bounds ell hell).1

theorem planeNodal_range_ne (ell : ℝ) (hell : 0 < ell) :
    (planeScalarEmbedding ell hell (planeNodal ell)).toLinearMap.range ≠
      (planeLLLEmbedding ell hell).toLinearMap.range := by
  intro h
  have hm : planeScalarEmbedding ell hell (planeNodal ell) (orbitalKet 0) ∈
      (planeLLLEmbedding ell hell).toLinearMap.range := by
    rw [← h]
    exact ⟨orbitalKet 0,rfl⟩
  have he := planeScalar_vacuum_mem_imp_constant ell hell (planeNodal ell) hm 0
    ((Real.pi/(2*planeNodalWaveNumber ell) : ℝ) : ℂ)
  rw [planeNodal_has_zero ell hell] at he
  change ((2*Real.cos (planeNodalWaveNumber ell*(0:ℂ).re)*Real.cos (planeNodalWaveNumber ell*(0:ℂ).im) : ℝ):ℂ) = 0 at he
  simp at he

/-- The improved reference constant occurs only in the explicit reference
sector hypotheses, for every k from zero through the chosen particle count. -/
theorem planeNodal_gap_of_reference_fifth (ell : ℝ) (hell : 0 < ell) (N : ℕ)
    (hgap : ∀ k ≤ N, (countablePairLift k planePairOperator * countablePairLift k planePairOperator -
      (1/5 : ℂ) • countablePairLift k planePairOperator).IsPositive) :
    ∀ t ∈ spectrum ℝ (planeBandContactOperator ell hell (planeNodal ell) (planeNodal_gram_strict ell hell)
      (planeNodal_differentiable ell) N), t = 0 ∨ (0.1763 : ℝ) ≤ t := by
  have h := physical_scalar_criterion ell hell (planeNodal ell) (planeNodal_differentiable ell)
    (1-0.004004) (1+0.004004) 1.98156 (1/5) (by norm_num) (by norm_num) (by norm_num)
    (planeNodal_gram_bounds ell hell).1 (planeNodal_gram_bounds ell hell).2
    (by convert planeNodal_pair_lower ell hell using 1) N
    (by simpa only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using hgap)
  intro t ht
  exact (h t ht).imp_right fun hb => le_trans (by norm_num) hb

/-- The projected Gram bound validates the maximal domain even at this nodal multiplier. -/
theorem planeNodal_maximal_domain (ell : ℝ) (hell : 0 < ell) :
    (Set.range (planeScalarEmbedding ell hell (planeNodal ell)) ∩
      (planeCoordinateDomain : Set (Lp ℂ 2 (volume : Measure ℂ)))) =
      planeAmbientMultiply (planeNodal ell) '' (Set.range (planeLLLEmbedding ell hell) ∩
        (planeCoordinateDomain : Set (Lp ℂ 2 (volume : Measure ℂ)))) :=
  planeBand_domain_intersection ell hell (planeNodal ell) (planeNodal_gram_strict ell hell)

end VortexGap.Fermion
