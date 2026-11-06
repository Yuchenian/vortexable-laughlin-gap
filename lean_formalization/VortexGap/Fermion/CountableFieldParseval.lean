import VortexGap.Fermion.CountablePairBounds
import VortexGap.Geometry.PlanePhysicalL2
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
namespace VortexGap.Fermion
open Filter
open scoped Topology

private theorem finiteModes {n N : ℕ} {y : Space n} (hy : InSector N y) :
    ∑ i ∈ Finset.range n, ‖countableAnnihilateMode i (countableEmbed n y)‖^2 = (N:ℝ)*‖y‖^2 := by
  rw [← Fin.sum_univ_eq_sum_range]
  simpa only [countableAnnihilateMode,countableTransition_embed,(countableEmbed n).norm_map]
    using sum_annihilateMode_norm_sq_of_sector hy

theorem countableMode_hasSum_number {N : ℕ} {x : CountableSpace} (hx : x ∈ countableSector N) :
    HasSum (fun i => ‖countableAnnihilateMode i x‖^2) ((N:ℝ)*‖x‖^2) := by
  have upper (m : ℕ) : ∑ i ∈ Finset.range m, ‖countableAnnihilateMode i x‖^2 ≤ (N:ℝ)*‖x‖^2 := by
    have hc : Continuous (fun y : CountableSpace => ∑ i ∈ Finset.range m, ‖countableAnnihilateMode i y‖^2) := by fun_prop
    apply le_of_tendsto ((hc.tendsto x).comp (countableEmbed_restrict_tendsto x))
    filter_upwards [eventually_ge_atTop m] with n hn
    calc
      _ ≤ ∑ i ∈ Finset.range n, ‖countableAnnihilateMode i (countableEmbed n (countableRestrict n x))‖^2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hn) (fun _ _ _ => sq_nonneg _)
      _ = _ := finiteModes (countableRestrict_sector hx)
      _ ≤ _ := mul_le_mul_of_nonneg_left ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
        (countableRestrict_norm_le n x)) (Nat.cast_nonneg _)
  have hs := summable_of_sum_range_le (fun i => sq_nonneg ‖countableAnnihilateMode i x‖) upper
  convert hs.hasSum using 1
  apply le_antisymm _ (hs.tsum_le_of_sum_range_le upper)
  have hlim := tendsto_const_nhds (x := (N:ℝ)) |>.mul ((countableEmbed_restrict_tendsto x).norm.pow 2)
  apply le_of_tendsto' hlim
  intro n
  rw [(countableEmbed n).norm_map, ← sum_annihilateMode_norm_sq_of_sector (countableRestrict_sector (n := n) hx)]
  calc
    _ ≤ ∑ i : Fin n, ‖countableAnnihilateMode i.val x‖^2 := by
      apply Finset.sum_le_sum
      intro i _
      have h := countableRestrict_transition i false x
      change countableRestrict n (countableAnnihilateMode i.val x) = annihilateMode i (countableRestrict n x) at h
      rw [← h]
      exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (countableRestrict_norm_le n _)
    _ ≤ _ := by rw [Fin.sum_univ_eq_sum_range (fun j => ‖countableAnnihilateMode j x‖^2) n]; exact hs.sum_le_tsum _ (fun _ _ => sq_nonneg _)

end VortexGap.Fermion
end

noncomputable section
namespace VortexGap.Fermion
open MeasureTheory
open scoped ENNReal
def creationProbe (y : CountableSpace) : CountableOrbital →L[ℂ] CountableSpace :=
  (ContinuousLinearMap.apply ℂ CountableSpace y).comp countableCreate

theorem fieldProbe_value (v : CountableOrbital) (x y : CountableSpace) :
    inner ℂ y (countableAnnihilate v x) = inner ℂ v ((creationProbe y).adjoint x) := by
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact ContinuousLinearMap.adjoint_inner_right _ _ _

theorem planeField_coefficient_parseval (ell : ℝ) (hell : 0 < ell) (x : CountableSpace) (A : Finset ℕ) :
    (∫ z : ℂ, ‖planeField ell z x A‖^2) = ∑' i, ‖countableAnnihilateMode i x A‖^2 := by
  let v := (creationProbe (countableKet A)).adjoint x
  have coeff (u : CountableOrbital) : countableAnnihilate u x A = inner ℂ u v := by
    rw [← countableKet_inner_left]
    exact fieldProbe_value _ _ _
  have hm (i : ℕ) : countableAnnihilateMode i x A = v i := by
    rw [← countableAnnihilate_ket,coeff,orbitalKet_inner_left]
  simp_rw [planeField,coeff,hm]
  rw [planeEvaluation_integral_norm_sq ell hell]
  simpa using lp.norm_rpow_eq_tsum (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal) v

end VortexGap.Fermion
end

noncomputable section
namespace VortexGap.Fermion
open MeasureTheory
open scoped ENNReal
theorem field_integral_of_coefficient_parseval {N : ℕ} (x : CountableSpace) (hx : x ∈ countableSector N)
    (field : ℂ → CountableSpace →L[ℂ] CountableSpace)
    (hi : ∀ A, Integrable (fun z => ‖field z x A‖^2) volume)
    (ha : ∀ A, (∫ z : ℂ, ‖field z x A‖^2) = ∑' i, ‖countableAnnihilateMode i x A‖^2) :
    (∫ z : ℂ, ‖field z x‖^2) = (N:ℝ)*‖x‖^2 := by
  let c := fun (i : ℕ) (A : Finset ℕ) => ‖countableAnnihilateMode i x A‖^2
  have hrow (i) : Summable (c i) := by
    simpa [c] using (lp.memℓp (countableAnnihilateMode i x)).summable
      (by norm_num : (0:ℝ)<(2:ℝ≥0∞).toReal)
  have hr (i) : ∑' A, c i A = ‖countableAnnihilateMode i x‖^2 := (countableSpace_norm_sq _).symm
  have hn := countableMode_hasSum_number hx
  have hs : Summable (Function.uncurry c) := by
    apply (summable_prod_of_nonneg (fun _ => sq_nonneg _)).mpr
    exact ⟨hrow,hn.summable.congr (fun i => (hr i).symm)⟩
  let F := fun (A : Finset ℕ) (z : ℂ) => ‖field z x A‖^2
  have hsum : Summable (fun A => ∫ z, ‖F A z‖) := by
    have hnorm (A z) : ‖F A z‖ = F A z := Real.norm_of_nonneg (sq_nonneg _)
    simp only [hnorm]
    exact (show Summable (fun A => ∑' i, c i A) from ((summable_prod_of_nonneg (fun p => sq_nonneg ‖countableAnnihilateMode p.2 x p.1‖)).mp hs.prod_symm).2).congr (fun A => (ha A).symm)
  calc
    _ = ∫ z : ℂ, ∑' A, F A z := integral_congr_ae (Filter.Eventually.of_forall (fun z => countableSpace_norm_sq _))
    _ = ∑' A, ∫ z, F A z := (integral_tsum_of_summable_integral_norm hi hsum).symm
    _ = ∑' A, ∑' i, c i A := tsum_congr ha
    _ = ∑' i, ∑' A, c i A := hs.tsum_comm
    _ = _ := (tsum_congr hr).trans hn.tsum_eq

theorem planeField_integral_number (ell : ℝ) (hell : 0<ell) {N : ℕ}
    (x : CountableSpace) (hx : x ∈ countableSector N) :
    (∫ z : ℂ, ‖planeField ell z x‖^2) = (N:ℝ)*‖x‖^2 := by
  apply field_integral_of_coefficient_parseval x hx _ _ (planeField_coefficient_parseval ell hell x)
  intro A
  let v := (creationProbe (countableKet A)).adjoint x
  have he (z : ℂ) : planeField ell z x A = inner ℂ (planeEvaluation ell z) v := by
    rw [← countableKet_inner_left]
    exact fieldProbe_value _ _ _
  simpa only [he] using (memLp_two_iff_integrable_sq_norm ((planeEvaluation_continuous ell).inner continuous_const).aestronglyMeasurable).mp (planeEvaluation_coefficient_memLp ell hell v)

theorem planeField_sector_memLp (ell : ℝ) (hell : 0<ell) {N : ℕ}
    (x : CountableSpace) (hx : x ∈ countableSector N) :
    MemLp (fun z => planeField ell z x) 2 volume := by
  have hc : Continuous (fun z => planeField ell z x) :=
    (countableAnnihilate_continuous.comp (planeEvaluation_continuous ell)).clm_apply continuous_const
  apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
  cases N with
  | zero =>
    simp only [planeField,countableAnnihilate_zero_sector _ hx,norm_zero,zero_pow (by decide : 2 ≠ 0)]
    exact integrable_zero _ _ _
  | succ n =>
    by_cases he : x=0
    · subst x; simp
    · apply Integrable.of_integral_ne_zero
      rw [planeField_integral_number ell hell x hx]
      exact mul_ne_zero (by positivity) (pow_ne_zero _ (norm_ne_zero_iff.mpr he))

end VortexGap.Fermion
end
