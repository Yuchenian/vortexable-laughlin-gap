import VortexGap.Fermion.ExteriorSquare
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.Tactic
noncomputable section
set_option autoImplicit false
namespace VortexGap.Frame
open MeasureTheory
open scoped ComplexConjugate Classical
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def unitColumn (v : E) : E := (‖v‖:ℂ)⁻¹ • v

def residualColumn (u v : E) : E := v - inner ℂ (unitColumn u) v • unitColumn u

theorem unitColumn_norm (v : E) (hv : v ≠ 0) : ‖unitColumn v‖ = 1 := by
  simp [unitColumn,norm_smul,hv]

theorem recover_unitColumn (v : E) : (‖v‖:ℂ) • unitColumn v = v := by
  by_cases h : v=0 <;> simp [unitColumn,h,smul_smul]

private theorem inner_unit {v : E} (hv : ‖v‖ = 1) : inner ℂ v v = 1 := by
  rw [inner_self_eq_norm_sq_to_K,hv]
  norm_num

theorem residualColumn_orthogonal (u v : E) : inner ℂ (unitColumn u) (unitColumn (residualColumn u v)) = 0 := by
  by_cases h : u=0
  · simp [h,unitColumn]
  · unfold unitColumn at ⊢
    rw [inner_smul_right]
    change _ * inner ℂ (unitColumn u) (residualColumn u v) = _
    rw [residualColumn,inner_sub_right,inner_smul_right,inner_unit (unitColumn_norm u h)]
    ring

private def twoColumnLinear (a b : E) : EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] E where
  toFun x := x 0 • a + x 1 • b
  map_add' _ _ := by simp only [PiLp.add_apply,add_smul]; abel
  map_smul' _ _ := by simp only [PiLp.smul_apply,smul_eq_mul,smul_add,smul_smul,RingHom.id_apply]

private def twoUnitFrame (a b : E) (ha : ‖a‖=1) (hb : ‖b‖=1) (hab : inner ℂ a b=0) :
    EuclideanSpace ℂ (Fin 2) →ₗᵢ[ℂ] E where
  toLinearMap := twoColumnLinear a b
  norm_map' := by
    apply (LinearMap.norm_map_iff_inner_map_map _).mpr
    intro x y
    change inner ℂ (x 0 • a + x 1 • b) (y 0 • a + y 1 • b) = _
    have hba := inner_eq_zero_symm.mp hab
    simp only [inner_add_left,inner_add_right,inner_smul_left,inner_smul_right,
      inner_unit ha,inner_unit hb,hab,hba,mul_zero,mul_one,zero_add,add_zero,
      PiLp.inner_apply,Fin.sum_univ_two,RCLike.inner_apply]

/-- A fixed frame on the vanishing-wedge locus keeps the label space unchanged. -/
def orthogonalPairFrame (base : EuclideanSpace ℂ (Fin 2) →ₗᵢ[ℂ] E) (u v : E) :
    EuclideanSpace ℂ (Fin 2) →ₗᵢ[ℂ] E := by
  classical
  exact if h : u ≠ 0 ∧ residualColumn u v ≠ 0 then
    twoUnitFrame _ _ (unitColumn_norm _ h.1) (unitColumn_norm _ h.2) (residualColumn_orthogonal u v)
  else base

theorem orthogonalPairFrame_column (base : EuclideanSpace ℂ (Fin 2) →ₗᵢ[ℂ] E) (u v : E) (j : Fin 2) :
    orthogonalPairFrame base u v (PiLp.single 2 j 1) =
      if u ≠ 0 ∧ residualColumn u v ≠ 0 then
        (if j=0 then unitColumn u else unitColumn (residualColumn u v))
      else base (PiLp.single 2 j 1) := by
  classical
  by_cases h : u ≠ 0 ∧ residualColumn u v ≠ 0
  · unfold orthogonalPairFrame
    rw [dite_eq_left h,ite_eq_left h]
    change (PiLp.single 2 j (1:ℂ) : EuclideanSpace ℂ (Fin 2)) 0 • unitColumn u + (PiLp.single 2 j (1:ℂ) : EuclideanSpace ℂ (Fin 2)) 1 • unitColumn (residualColumn u v) = _
    fin_cases j <;> simp
  · simp [orthogonalPairFrame,h]

/-- Wedge area before normalization; dependent or zero columns have weight zero. -/
def pairColumnArea (u v : E) : ℝ := ‖u‖ * ‖residualColumn u v‖

theorem alternating_pair_normalize {F : Type*} [AddCommGroup F] [Module ℂ F]
    (W : E →ₗ[ℂ] E →ₗ[ℂ] F) (halt : ∀ x, W x x = 0)
    (base : EuclideanSpace ℂ (Fin 2) →ₗᵢ[ℂ] E) (u v : E) :
    let T := orthogonalPairFrame base u v
    W u v = (pairColumnArea u v : ℂ) • W (T (PiLp.single 2 0 1)) (T (PiLp.single 2 1 1)) := by
  let a := unitColumn u
  let r := residualColumn u v
  have ha : (‖u‖:ℂ) • a = u := recover_unitColumn u
  have hr : (‖r‖:ℂ) • unitColumn r = r := recover_unitColumn r
  have hv : W a r = W a v := by simp [r,residualColumn,a,halt]
  have hw : W u v = (pairColumnArea u v:ℂ) • W a (unitColumn r) := by
    calc W u v = (‖u‖:ℂ) • W a v := by conv_lhs => rw [← ha,map_smul,LinearMap.smul_apply]
         _ = (‖u‖:ℂ) • W a r := by rw [hv]
         _ = _ := by
           conv_lhs => rw [← hr,map_smul,smul_smul]
           simp [pairColumnArea,r]
  dsimp only
  by_cases h : u ≠ 0 ∧ residualColumn u v ≠ 0
  · simpa [orthogonalPairFrame_column,h,a,r] using hw
  · have hz : pairColumnArea u v = 0 := by
      by_cases hu : u=0
      · simp [pairColumnArea,hu]
      · have hr0 : residualColumn u v = 0 := by_contra fun hr0 => h ⟨hu,hr0⟩
        simp [pairColumnArea,hr0]
    simpa only [hz,Complex.ofReal_zero,zero_smul] using hw

theorem pairColumnArea_nonneg (u v : E) : 0 ≤ pairColumnArea u v :=
  mul_nonneg (norm_nonneg _) (norm_nonneg _)

/-- Square of the absorbed coefficient, computed directly from the two raw columns. -/
theorem pairColumnArea_sq (u v : E) :
    pairColumnArea u v ^ 2 = ‖u‖^2 * ‖v‖^2 - ‖inner ℂ u v‖^2 := by
  by_cases h : u=0
  · simp [h,pairColumnArea]
  let a := unitColumn u
  let r := residualColumn u v
  let z := inner ℂ a v
  have ha : ‖a‖ = 1 := unitColumn_norm u h
  have har : inner ℂ a r = 0 := by
    change inner ℂ a (v - inner ℂ a v • a) = 0
    rw [inner_sub_right,inner_smul_right,inner_unit ha,mul_one,sub_self]
  have hvr : z • a + r = v := add_sub_cancel _ _
  have hv := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (z • a) r
    (by rw [inner_smul_left,har,mul_zero])
  rw [hvr,norm_smul,ha,mul_one] at hv
  have hi : ‖inner ℂ u v‖ = ‖u‖ * ‖z‖ := by
    conv_lhs => rw [← recover_unitColumn u,inner_smul_left,norm_mul,RCLike.norm_conj,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
  change (‖u‖*‖r‖)^2 = _
  rw [hi,pow_two ‖v‖,hv]
  ring

theorem pairColumnArea_le (u v : E) : pairColumnArea u v ≤ ‖u‖*‖v‖ := by
  apply (sq_le_sq₀ (pairColumnArea_nonneg u v) (mul_nonneg (norm_nonneg u) (norm_nonneg v))).mp
  rw [pairColumnArea_sq,mul_pow]
  exact sub_le_self _ (sq_nonneg _)

/-- The coefficient absorbing the normalization is exactly the wedge norm for the usual
isometric exterior product, also at rank-deficient labels. -/
theorem alternating_pair_area_eq_norm {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (W : E →ₗ[ℂ] E →ₗ[ℂ] F) (halt : ∀ x, W x x = 0)
    (hunit : ∀ T : EuclideanSpace ℂ (Fin 2) →ₗᵢ[ℂ] E,
      ‖W (T (PiLp.single 2 0 1)) (T (PiLp.single 2 1 1))‖ = 1)
    (base : EuclideanSpace ℂ (Fin 2) →ₗᵢ[ℂ] E) (u v : E) :
    pairColumnArea u v = ‖W u v‖ := by
  rw [alternating_pair_normalize W halt base u v,norm_smul,hunit,mul_one,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (pairColumnArea_nonneg u v)]

theorem alternating_expansion_normalize {F I : Type*} [AddCommGroup F] [Module ℂ F] [Fintype I]
    (W : E →ₗ[ℂ] E →ₗ[ℂ] F) (halt : ∀ x, W x x = 0)
    (base : EuclideanSpace ℂ (Fin 2) →ₗᵢ[ℂ] E) (c : I → ℂ) (u v : I → E) :
    let T := fun i => orthogonalPairFrame base (u i) (v i)
    (∑ i, c i • W (u i) (v i)) = ∑ i, (c i * (pairColumnArea (u i) (v i):ℂ)) •
      W (T i (PiLp.single 2 0 1)) (T i (PiLp.single 2 1 1)) := by
  apply Finset.sum_congr rfl
  intro i _
  rw [alternating_pair_normalize W halt base (u i) (v i),smul_smul]

section Measurability
variable {α : Type*} [MeasurableSpace α] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem measurable_unitColumn {u : α → E} (hu : Measurable u) : Measurable (fun x => unitColumn (u x)) :=
  ((Complex.continuous_ofReal.measurable.comp hu.norm).inv).smul hu

theorem measurable_residualColumn {u v : α → E} (hu : Measurable u) (hv : Measurable v) :
    Measurable (fun x => residualColumn (u x) (v x)) :=
  hv.sub (((measurable_unitColumn hu).inner hv).smul (measurable_unitColumn hu))

theorem measurable_pairColumnArea {u v : α → E} (hu : Measurable u) (hv : Measurable v) :
    Measurable (fun x => pairColumnArea (u x) (v x)) := hu.norm.mul (measurable_residualColumn hu hv).norm

theorem measurable_orthogonalPairFrame_column (base : EuclideanSpace ℂ (Fin 2) →ₗᵢ[ℂ] E)
    {u v : α → E} (hu : Measurable u) (hv : Measurable v) (j : Fin 2) :
    Measurable (fun x => orthogonalPairFrame base (u x) (v x) (PiLp.single 2 j 1)) := by
  simp_rw [orthogonalPairFrame_column]
  have hr := measurable_residualColumn hu hv
  apply Measurable.ite ((measurableSet_eq_fun hu measurable_const).compl.inter (measurableSet_eq_fun hr measurable_const).compl) _ measurable_const
  by_cases hj : j=0
  · simpa [hj] using measurable_unitColumn hu
  · simpa [hj] using measurable_unitColumn hr


theorem aestronglyMeasurable_orthogonalPairFrame_column (base : EuclideanSpace ℂ (Fin 2) →ₗᵢ[ℂ] E)
    {μ : Measure α} {u v : α → E} (hu : AEStronglyMeasurable u μ) (hv : AEStronglyMeasurable v μ) (j : Fin 2) :
    AEStronglyMeasurable (fun x => orthogonalPairFrame base (u x) (v x) (PiLp.single 2 j 1)) μ := by
  have h := measurable_orthogonalPairFrame_column base (α := E × E) measurable_fst measurable_snd j
  exact (h.comp_aemeasurable (hu.prodMk hv).aemeasurable).aestronglyMeasurable

theorem aestronglyMeasurable_pairColumnArea {μ : Measure α} {u v : α → E}
    (hu : AEStronglyMeasurable u μ) (hv : AEStronglyMeasurable v μ) :
    AEStronglyMeasurable (fun x => pairColumnArea (u x) (v x)) μ := by
  have h := measurable_pairColumnArea (α := E × E) measurable_fst measurable_snd
  exact (h.comp_aemeasurable (hu.prodMk hv).aemeasurable).aestronglyMeasurable

/-- Local L² is preserved under reweighting when the raw column norms are bounded.
Applied to a restricted measure this needs only a local bound. -/
theorem memLp_pairAreaCoefficient {μ : Measure α} {c : α → ℂ} {u v : α → E}
    (hc : MemLp c 2 μ) (hu : AEStronglyMeasurable u μ) (hv : AEStronglyMeasurable v μ)
    (K : ℝ) (hK : ∀ᵐ x ∂μ, ‖u x‖*‖v x‖ ≤ K) :
    MemLp (fun x => c x * (pairColumnArea (u x) (v x):ℂ)) 2 μ := by
  have hm := Complex.continuous_ofReal.comp_aestronglyMeasurable (aestronglyMeasurable_pairColumnArea hu hv)
  apply hc.of_le_mul (c := K) (hc.aestronglyMeasurable.mul hm)
  filter_upwards [hK] with x hx
  change ‖c x * (pairColumnArea (u x) (v x):ℂ)‖ ≤ K * ‖c x‖
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (pairColumnArea_nonneg _ _),mul_comm K]
  exact mul_le_mul_of_nonneg_left ((pairColumnArea_le _ _).trans hx) (norm_nonneg _)

end Measurability
end VortexGap.Frame
