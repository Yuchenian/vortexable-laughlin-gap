import VortexGap.Fermion.CountablePairFilterAdjoint
import VortexGap.Transfer.CountableSlater
import VortexGap.Examples.CountableContinuousMix
import VortexGap.Examples.CountableLabelBessel
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open VortexGap.Frame VortexGap.Examples MeasureTheory
open scoped InnerProduct ENNReal
def infiniteCellIndex (j : ℕ) (a : Fin 2) : CountablePairIndex :=
  ⟨(4*j+2*a.val,4*j+2*a.val+1),by dsimp; omega⟩
def infiniteCellFrames (j : ℕ) (a : Fin 2) := countableModeFrame (infiniteCellIndex j a)
def infiniteCellCoeff (_ : ℕ) : Fin 2 → ℂ := ![1,Complex.I]

private theorem mode_overlap_zero (p q : CountablePairIndex) (h00 : p.val.1 ≠ q.val.1)
    (h01 : p.val.1 ≠ q.val.2) (h10 : p.val.2 ≠ q.val.1) (h11 : p.val.2 ≠ q.val.2) :
    countableTwoFrameOverlap (countableModeFrame p) (countableModeFrame q) = 0 := by
  apply (EuclideanSpace.basisFun (Fin 2) ℂ).toBasis.ext
  intro j
  simp only [OrthonormalBasis.coe_toBasis,EuclideanSpace.basisFun_apply]
  ext i
  change countableTwoFrameOverlap _ _ (PiLp.single 2 j 1) i = 0
  rw [countableTwoFrameOverlap_entry]
  fin_cases i <;> fin_cases j <;>
    simp [countableModeFrame_first,countableModeFrame_second,orbitalKet,lp.inner_single_left,lp.single_apply,
      h00,h01,h10,h11]

private theorem cellTrace (i j : ℕ) (a b : Fin 2) :
    traceNormTwo (countableTwoFrameOverlap (infiniteCellFrames i a) (infiniteCellFrames j b)) =
      if i=j ∧ a=b then 2 else 0 := by
  split_ifs with h
  · obtain ⟨rfl,rfl⟩ := h
    rw [countableTwoFrameOverlap_self,traceNormTwo_id]
  · rw [infiniteCellFrames,infiniteCellFrames,mode_overlap_zero,traceNormTwo_zero] <;>
      dsimp [infiniteCellIndex] <;> have hh : ¬(i=j ∧ a.val=b.val) := fun hh => h ⟨hh.1,Fin.ext hh.2⟩ <;> omega

theorem infiniteCell_kernel (i j : ℕ) :
    countableSlaterKernel (infiniteCellCoeff i) (infiniteCellCoeff j) (infiniteCellFrames i) (infiniteCellFrames j) =
      if i=j then 4 else 0 := by
  by_cases h : i=j <;> norm_num [countableSlaterKernel,Fin.sum_univ_two,infiniteCellCoeff,cellTrace,h]

theorem infiniteCell_row (i : ℕ) :
    (∫ j, countableSlaterKernel (infiniteCellCoeff i) (infiniteCellCoeff j) (infiniteCellFrames i) (infiniteCellFrames j)
      ∂(Measure.count : Measure ℕ)) = 4 := by
  simp_rw [infiniteCell_kernel]
  have he : (fun j : ℕ => if i=j then (4:ℝ) else 0) = Set.indicator {i} (fun _ => 4) := by
    funext j
    by_cases h : i=j <;> simp [h,Ne.symm]
  rw [he,integral_indicator (measurableSet_singleton _)]
  simp

theorem infiniteCellPair_formula (j : ℕ) :
    countableSlaterPair (infiniteCellCoeff j) (infiniteCellFrames j) =
    lp.single 2 (infiniteCellIndex j 0) 1 + Complex.I • lp.single 2 (infiniteCellIndex j 1) 1 := by
  simp [countableSlaterPair,infiniteCellCoeff,infiniteCellFrames,Fin.sum_univ_two,countableModeFrame_first,
    countableModeFrame_second,countableWedge_basis]

theorem infiniteCellPair_norm_sq (j : ℕ) : ‖countableSlaterPair (infiniteCellCoeff j) (infiniteCellFrames j)‖^2 = 2 := by
  have hne : infiniteCellIndex j 0 ≠ infiniteCellIndex j 1 := by
    intro he
    have hv := congrArg (fun p : CountablePairIndex => p.val.1) he
    simp [infiniteCellIndex] at hv
  rw [infiniteCellPair_formula, pow_two, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ)]
  · norm_num [norm_smul,countableModePair_norm]
  · simp [inner_smul_right,lp.inner_single_left,lp.single_apply,hne]

theorem infiniteCellPair_not_global_L2 :
    ¬ MemLp (fun j => countableSlaterPair (infiniteCellCoeff j) (infiniteCellFrames j)) 2 (Measure.count : Measure ℕ) := by
  intro h
  have hi := (memLp_two_iff_integrable_sq_norm h.aestronglyMeasurable).mp h
  simp_rw [infiniteCellPair_norm_sq] at hi
  have hf := (integrable_const_iff_isFiniteMeasure (by norm_num : (2:ℝ) ≠ 0)).mp hi
  exact (ne_of_lt hf.measure_univ_lt_top) countableLabel_measure_infinite

private theorem infiniteCell_row_integrable (i : ℕ) :
    Integrable (fun j => countableSlaterKernel (infiniteCellCoeff i) (infiniteCellCoeff j)
      (infiniteCellFrames i) (infiniteCellFrames j) * 1) (Measure.count : Measure ℕ) := by
  simp_rw [mul_one,infiniteCell_kernel]
  apply integrable_count_iff.mpr
  apply summable_of_ne_finset_zero (s := {i})
  intro j hj
  simp_all [eq_comm]

theorem infiniteCell_global_analysis (y : CountableSpace) :
    let R := fun j => countableSlaterColumn countableMixFilter (infiniteCellCoeff j) (infiniteCellFrames j)
    MemLp (fun j => (R j).adjoint y) 2 Measure.count ∧
    (∫ j, ‖(R j).adjoint y‖^2 ∂Measure.count) ≤ 4*‖y‖^2 := by
  apply countableSlater_global_bessel Measure.count countableMixFilter infiniteCellCoeff infiniteCellFrames
    countableMixFilter_contraction _ _ (fun _ => 1) (fun _ => zero_lt_one) aestronglyMeasurable_const 4
    (by norm_num) (Filter.Eventually.of_forall infiniteCell_row_integrable)
    (Filter.Eventually.of_forall fun i => by simpa only [mul_one] using (infiniteCell_row i).le)
  · intro n i
    have : IsFiniteMeasure ((Measure.count : Measure ℕ).restrict (spanningSets Measure.count n)) :=
      isFiniteMeasure_restrict.mpr (measure_spanningSets_lt_top Measure.count n).ne
    exact memLp_const _
  · intro i l
    exact (continuous_of_discreteTopology : Continuous (fun j => infiniteCellFrames j i (PiLp.single 2 l 1))).aestronglyMeasurable

def infiniteCellPair (j : ℕ) := countableSlaterPair (infiniteCellCoeff j) (infiniteCellFrames j)

theorem infiniteCell_inner (i j : ℕ) : inner ℂ (infiniteCellPair i) (infiniteCellPair j) = if i=j then 2 else 0 := by
  by_cases hij : i=j
  · subst j
    simp only [inner_self_eq_norm_sq_to_K,← RCLike.ofReal_pow,infiniteCellPair,infiniteCellPair_norm_sq]
    rfl
  · have hn (a b : Fin 2) : infiniteCellIndex i a ≠ infiniteCellIndex j b := by
      intro h
      have hh := congrArg (fun k : CountablePairIndex => k.val.1) h
      dsimp [infiniteCellIndex] at hh
      omega
    simp [infiniteCellPair,infiniteCellPair_formula,
      lp.inner_single_left,lp.single_apply,hn,hij]

private def unitCell (i : ℕ) := ((Real.sqrt 2 : ℂ)⁻¹) • infiniteCellPair i

private theorem unitCell_orthonormal : Orthonormal ℂ unitCell := by
  rw [orthonormal_iff_ite]
  intro i j
  by_cases h : i=j
  · subst j
    rw [unitCell,inner_smul_left,inner_smul_right,infiniteCell_inner]
    simp only [ite_true, map_inv₀, Complex.conj_ofReal]
    have hs : (↑(Real.sqrt 2) : ℂ)^2 = 2 := by exact_mod_cast Real.sq_sqrt (by norm_num : 0 ≤ (2:ℝ))
    field_simp
    linear_combination -hs
  · simp [unitCell,inner_smul_left,inner_smul_right,infiniteCell_inner,h]

private theorem cellScale (j : ℕ) (q : CountablePairSpace) :
    ‖inner ℂ (infiniteCellPair j) q‖^2 = 2*‖inner ℂ (unitCell j) q‖^2 := by
  simp only [unitCell,inner_smul_left,norm_mul,Complex.norm_conj,norm_inv,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),mul_pow,inv_pow,Real.sq_sqrt (by norm_num : 0 ≤ (2:ℝ))]
  ring

theorem infiniteCell_coeff_L2 (q : CountablePairSpace) :
    MemLp (fun j => inner ℂ (infiniteCellPair j) q) 2 Measure.count := by
  apply (memLp_two_iff_integrable_sq_norm continuous_of_discreteTopology.aestronglyMeasurable).mpr
  apply integrable_count_iff.mpr
  simpa only [Real.norm_eq_abs,abs_sq,abs_norm,cellScale,abs_mul,abs_of_nonneg (by norm_num : 0 ≤ (2:ℝ))] using (unitCell_orthonormal.inner_products_summable q).mul_left 2

theorem infiniteCell_pair_bessel (q : CountablePairSpace) :
    (∫ j, ‖inner ℂ (infiniteCellPair j) q‖^2 ∂Measure.count) ≤ 2*‖q‖^2 := by
  have hi := (memLp_two_iff_integrable_sq_norm (infiniteCell_coeff_L2 q).aestronglyMeasurable).mp (infiniteCell_coeff_L2 q)
  rw [integral_countable hi]
  simp only [count_real_singleton,one_smul,cellScale,tsum_mul_left]
  exact mul_le_mul_of_nonneg_left (unitCell_orthonormal.tsum_inner_products_le q) (by norm_num)

def infiniteCellQ := countableContinuousPairOperator Measure.count infiniteCellPair infiniteCell_coeff_L2
  2 (by norm_num) infiniteCell_pair_bessel

theorem infiniteCellQ_coeff (i : ℕ) (q : CountablePairSpace) :
    inner ℂ (infiniteCellPair i) (infiniteCellQ q) = 2 * inner ℂ (infiniteCellPair i) q := by
  rw [infiniteCellQ,countableContinuousPairOperator_inner]
  simp_rw [infiniteCell_inner]
  have he : (fun j : ℕ => inner ℂ (if j=i then (2:ℂ) else 0) (inner ℂ (infiniteCellPair j) q)) =
      Set.indicator {i} (fun _ => 2*inner ℂ (infiniteCellPair i) q) := by
    funext j
    by_cases h : j=i <;> simp [h, RCLike.inner_apply, map_ofNat,mul_comm]
  rw [he,integral_indicator (measurableSet_singleton _)]
  simp

theorem infiniteCellQ_square : infiniteCellQ * infiniteCellQ = (2:ℂ) • infiniteCellQ := by
  ext q : 1
  apply ext_inner_left ℂ
  intro r
  change inner ℂ r (infiniteCellQ (infiniteCellQ q)) = inner ℂ r ((2:ℂ) • infiniteCellQ q)
  rw [inner_smul_right]
  rw [show inner ℂ r (infiniteCellQ (infiniteCellQ q)) = _ from
    countableContinuousPairOperator_inner Measure.count _ infiniteCell_coeff_L2 2 _ infiniteCell_pair_bessel r (infiniteCellQ q)]
  simp_rw [infiniteCellQ_coeff]
  simp only [RCLike.inner_apply]
  simp_rw [mul_assoc (2:ℂ)]
  rw [integral_const_mul,infiniteCellQ,countableContinuousPairOperator_inner]
  rfl

private theorem infiniteCell_lift_square :
    countablePairLift 2 infiniteCellQ * countablePairLift 2 infiniteCellQ = (2:ℂ) • countablePairLift 2 infiniteCellQ := by
  apply ContinuousLinearMap.ext
  intro x
  let q := countablePairCoordinates x
  have hx : x = ⟨countablePairEmbedding q,countablePairEmbedding_sector q⟩ := Subtype.ext (countablePairEmbedding_coordinates x.property).symm
  rw [hx]
  simp only [mul_apply_eq_comp,smul_apply,countablePairLift_pairEmbedding]
  apply Subtype.ext
  change countablePairEmbedding (infiniteCellQ (infiniteCellQ q)) = (2:ℂ) • countablePairEmbedding (infiniteCellQ q)
  rw [← map_smul]
  exact congrArg countablePairEmbedding (DFunLike.congr_fun infiniteCellQ_square q)


theorem infiniteCell_two_gap (x : countableSector 2) :
    let H := countableContinuousFilteredHamiltonian Measure.count infiniteCellPair infiniteCell_coeff_L2
      2 (by norm_num) infiniteCell_pair_bessel countableMixFilter countableMixFilter_nonneg 2
    (2-4*(199/10000:ℝ)-2*(199/10000:ℝ)^2)*(inner ℂ x (H x)).re ≤ ‖H x‖^2 := by
  have hh := countableSlater_transfer_norm Measure.count infiniteCellPair infiniteCell_coeff_L2
    2 (by norm_num) infiniteCell_pair_bessel countableMixFilter countableMixFilter_nonneg countableMixFilter_contraction
    infiniteCellCoeff infiniteCellFrames (fun _ => rfl)
    (fun n i => by
      have : IsFiniteMeasure ((Measure.count : Measure ℕ).restrict (spanningSets Measure.count n)) :=
        isFiniteMeasure_restrict.mpr (measure_spanningSets_lt_top Measure.count n).ne
      exact memLp_const _)
    (fun _ _ => continuous_of_discreteTopology.aestronglyMeasurable)
    (fun _ => 1) (fun _ => zero_lt_one) aestronglyMeasurable_const 4 (by norm_num)
    (Filter.Eventually.of_forall infiniteCell_row_integrable)
    (Filter.Eventually.of_forall fun i => by simpa only [mul_one] using (infiniteCell_row i).le)
    2 2 (fun k hk => by
      change (countablePairLift k infiniteCellQ * countablePairLift k infiniteCellQ - (2:ℂ) • countablePairLift k infiniteCellQ).IsPositive
      have he : countablePairLift k infiniteCellQ * countablePairLift k infiniteCellQ = (2:ℂ) • countablePairLift k infiniteCellQ := by
        interval_cases k
        · rw [countablePairLift_zero_sector,zero_mul]; ext z : 1; simp [smul_apply]
        · rw [countablePairLift_one_sector,zero_mul]; ext z : 1; simp [smul_apply]
        · exact infiniteCell_lift_square
      have hz : countablePairLift k infiniteCellQ * countablePairLift k infiniteCellQ - (2:ℂ) • countablePairLift k infiniteCellQ = 0 := by
        rw [he]; ext z : 1; simp
      rw [hz]; exact ContinuousLinearMap.isPositive_zero) x
  simpa only [countableMixFilter_delta] using hh

private theorem fixed_pair :
    countablePairFilter countableMixFilter countableMixFilter_nonneg (infiniteCellPair 1) = infiniteCellPair 1 := by
  have hfix (j : ℕ) (h : 4 ≤ j) : countableMixFilter (orbitalKet j) = orbitalKet j := by
    ext i
    rw [countableMixFilter_entry,countableMixVector_apply]
    simp [show j≠0 by omega,show j≠2 by omega,orbitalKet,lp.single_apply,Pi.single_apply,eq_comm]
  have ha (a : Fin 2) : countablePairFilter countableMixFilter countableMixFilter_nonneg
      (lp.single 2 (infiniteCellIndex 1 a) 1) = lp.single 2 (infiniteCellIndex 1 a) 1 := by
    rw [← countableWedge_basis,countablePairFilter_wedge,hfix _ (by dsimp [infiniteCellIndex]; omega),
      hfix _ (by dsimp [infiniteCellIndex]; omega)]
  simp only [infiniteCellPair,infiniteCellPair_formula,map_add,map_smul,ha]

theorem infiniteCell_filtered_eigen :
    let v : countableSector 2 := ⟨countablePairEmbedding (infiniteCellPair 1),countablePairEmbedding_sector _⟩
    let H := countableContinuousFilteredHamiltonian Measure.count infiniteCellPair infiniteCell_coeff_L2
      2 (by norm_num) infiniteCell_pair_bessel countableMixFilter countableMixFilter_nonneg 2
    H v = (2:ℂ) • v ∧ ‖v‖^2 = 2 := by
  dsimp only
  constructor
  · have hQ : infiniteCellQ (infiniteCellPair 1) = (2:ℂ) • infiniteCellPair 1 := by
      apply ext_inner_right ℂ
      intro q
      have hA := countableContinuousPairOperator_positive Measure.count infiniteCellPair
        infiniteCell_coeff_L2 2 (by norm_num) infiniteCell_pair_bessel
      change infiniteCellQ.IsPositive at hA
      rw [show inner ℂ (infiniteCellQ (infiniteCellPair 1)) q = inner ℂ (infiniteCellPair 1) (infiniteCellQ q) from hA.isSymmetric _ _,infiniteCellQ_coeff,inner_smul_left]
      simp [map_ofNat]
    rw [countableContinuousFilteredHamiltonian,countablePairLift_pairEmbedding]
    apply Subtype.ext
    change countablePairEmbedding ((countablePairFilter countableMixFilter countableMixFilter_nonneg)
      (infiniteCellQ ((countablePairFilter countableMixFilter countableMixFilter_nonneg).adjoint (infiniteCellPair 1)))) = _
    rw [countablePairFilter_adjoint,fixed_pair,hQ,map_smul,fixed_pair,map_smul]
    rfl
  · change ‖countablePairEmbedding (infiniteCellPair 1)‖^2 = 2
    rw [countablePairEmbedding.norm_map]
    exact infiniteCellPair_norm_sq _

end VortexGap.Fermion
