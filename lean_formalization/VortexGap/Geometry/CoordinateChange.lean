import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.ContDiff.Operations
import VortexGap.Frame.L2FiniteFiber

noncomputable section

namespace VortexGap.Fermion
open MeasureTheory
def coordinateJacobian (F : ℂ → ℂ) (z : ℂ) : ℝ := (fderiv ℝ F z).det

theorem coordinateJacobian_axes (F : ℂ → ℂ) (z : ℂ) :
    coordinateJacobian F z =
    ((fderiv ℝ F z) 1).re * ((fderiv ℝ F z) Complex.I).im -
      ((fderiv ℝ F z) Complex.I).re * ((fderiv ℝ F z) 1).im := by
  change (fderiv ℝ F z).toLinearMap.det = _
  rw [← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, Complex.coe_basisOneI_repr]

theorem coordinateJacobian_diff (F : ℂ → ℂ) (hf : ContDiff ℝ 2 F) :
    Differentiable ℝ (coordinateJacobian F) := by
  have hd : Differentiable ℝ (fderiv ℝ F) := (hf.fderiv_right (m := 1) (by decide)).differentiable_one
  have he : coordinateJacobian F = _ := funext (coordinateJacobian_axes F)
  rw [he]
  fun_prop

theorem coordinateChange_integral (F : ℂ ≃ₜ ℂ) (hf : Differentiable ℝ F)
    (hJ : ∀ z, 0 < coordinateJacobian F z) (d : ℂ → ℝ) :
    (∫ z, coordinateJacobian F z * d (F z)) = ∫ w, d w := by
  have h := integral_image_eq_integral_abs_det_fderiv_smul (volume : Measure ℂ)
    MeasurableSet.univ (fun z _ => (hf z).hasFDerivAt.hasFDerivWithinAt) F.injective.injOn d
  have hpos (z : ℂ) : 0 < (fderiv ℝ (⇑F) z).det := hJ z
  simpa only [Set.image_univ, F.surjective.range_eq, Measure.restrict_univ, smul_eq_mul,
    coordinateJacobian, abs_of_pos (hpos _)] using h.symm

def coordinateMetricWeight (F : ℂ ≃ₜ ℂ) (w : ℂ) : ℝ :=
  let z := F.symm w
  coordinateJacobian F z * (‖fderiv ℝ F z 1‖^2 + ‖fderiv ℝ F z Complex.I‖^2)/2

theorem coordinateMetricWeight_continuous (F : ℂ ≃ₜ ℂ) (hf : ContDiff ℝ 2 F) :
    Continuous (coordinateMetricWeight F) := by
  have hd : Continuous (fderiv ℝ F) := hf.continuous_fderiv (by decide)
  have hj := (coordinateJacobian_diff F hf).continuous
  unfold coordinateMetricWeight
  fun_prop

end VortexGap.Fermion

namespace VortexGap.Fermion
open MeasureTheory Filter
local notation "H" => Lp ℂ 2 (volume : Measure ℂ)
variable (F : ℂ ≃ₜ ℂ) (hf : ContDiff ℝ 2 F) (hJ : ∀ z, 0 < coordinateJacobian F z)

include hf hJ
private theorem weightedMap :
    Measure.map F (volume.withDensity (fun z => ENNReal.ofReal (coordinateJacobian F z))) = volume := by
  have h := map_withDensity_abs_det_fderiv_eq_addHaar (volume : Measure ℂ) MeasurableSet.univ.nullMeasurableSet
    (fun z _ => ((hf.differentiable (by decide)) z).hasFDerivAt.hasFDerivWithinAt) F.injective.injOn
  have hp (z : ℂ) : 0 < (fderiv ℝ (⇑F) z).det := hJ z
  simpa only [Set.image_univ,F.surjective.range_eq,Measure.restrict_univ,coordinateJacobian,abs_of_pos (hp _)] using h

theorem coordinate_ae_iff (P : ℂ → Prop) : (∀ᵐ z ∂volume, P (F z)) ↔ ∀ᵐ w ∂volume, P w := by
  let ρ := fun z => ENNReal.ofReal (coordinateJacobian F z)
  have hm : AEMeasurable ρ volume := (ENNReal.continuous_ofReal.comp (coordinateJacobian_diff F hf).continuous).aemeasurable
  have hn : ∀ᵐ z ∂volume, ρ z ≠ 0 := Eventually.of_forall (fun z => (ENNReal.ofReal_pos.mpr (hJ z)).ne')
  have h1 := withDensity_absolutelyContinuous' hm hn
  have h2 := withDensity_absolutelyContinuous volume ρ
  have he := F.measurableEmbedding.ae_map_iff (μ := volume.withDensity ρ) (p := P)
  rw [weightedMap F hf hJ] at he
  exact ⟨fun h => he.mpr (h2.ae_le h), fun h => h1.ae_le (he.mp h)⟩

private theorem jac_integrable_iff (d : ℂ → ℝ) :
    Integrable d ↔ Integrable (fun z => coordinateJacobian F z * d (F z)) := by
  have h := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul (volume : Measure ℂ) MeasurableSet.univ
    (fun z _ => ((hf.differentiable (by decide)) z).hasFDerivAt.hasFDerivWithinAt) F.injective.injOn d
  have hp (z : ℂ) : 0 < (fderiv ℝ (⇑F) z).det := hJ z
  simpa only [Set.image_univ,F.surjective.range_eq,integrableOn_univ,smul_eq_mul,coordinateJacobian,
    abs_of_pos (hp _)] using h

private def jacRoot (z : ℂ) : ℂ := ((Real.sqrt (coordinateJacobian F z) : ℝ) : ℂ)
omit hf in
private theorem jacNorm (g : ℂ → ℂ) (z : ℂ) :
    ‖jacRoot F z * g (F z)‖^2 = coordinateJacobian F z * ‖g (F z)‖^2 := by
  rw [norm_mul,mul_pow]
  simp only [jacRoot,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (hJ z).le]

private theorem pull_mem_iff (g : ℂ → ℂ) (hg : StronglyMeasurable g) :
    MemLp g 2 volume ↔ MemLp (fun z => jacRoot F z * g (F z)) 2 volume := by
  have hm : Continuous (jacRoot F) := Complex.continuous_ofReal.comp (coordinateJacobian_diff F hf).continuous.sqrt
  have hs : AEStronglyMeasurable (fun z => jacRoot F z * g (F z)) volume := (hm.stronglyMeasurable.mul (hg.comp_measurable F.continuous.measurable)).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable,
    memLp_two_iff_integrable_sq_norm hs]
  simp_rw [jacNorm F hJ]
  exact jac_integrable_iff F hf hJ _

private def jacPull (u : H) : H :=
  ((pull_mem_iff F hf hJ u (Lp.stronglyMeasurable u)).mp (Lp.memLp u)).toLp _

private theorem jacPull_ae (u : H) :
    (jacPull F hf hJ u : ℂ → ℂ) =ᵐ[volume] fun z => jacRoot F z * u (F z) :=
  MemLp.coeFn_toLp _

private def jacIsometry : H →ₗᵢ[ℂ] H where
  toFun := jacPull F hf hJ
  map_add' u v := by
    apply Lp.ext
    have hc := (coordinate_ae_iff F hf hJ (fun w => (u+v) w = u w + v w)).mpr (by simpa only [Filter.EventuallyEq,Pi.add_apply] using! Lp.coeFn_add u v)
    filter_upwards [jacPull_ae F hf hJ (u+v),jacPull_ae F hf hJ u,jacPull_ae F hf hJ v,
      Lp.coeFn_add (jacPull F hf hJ u) (jacPull F hf hJ v), hc] with z hs hu hv ha hc
    simp only [hs,ha,Pi.add_apply,hu,hv,hc,mul_add]
  map_smul' c u := by
    apply Lp.ext
    have hc := (coordinate_ae_iff F hf hJ (fun w => (c • u) w = c • u w)).mpr (by simpa only [Filter.EventuallyEq,Pi.smul_apply] using! Lp.coeFn_smul c u)
    filter_upwards [jacPull_ae F hf hJ (c • u),jacPull_ae F hf hJ u,Lp.coeFn_smul c (jacPull F hf hJ u),hc]
      with z hs hu ha hc
    simp only [RingHom.id_apply,hs,ha,Pi.smul_apply,hu,hc,smul_eq_mul]; ring
  norm_map' u := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [Frame.l2_norm_sq_integral,Frame.l2_norm_sq_integral,
      ← coordinateChange_integral F (hf.differentiable (by decide)) hJ (fun w => ‖u w‖^2)]
    apply integral_congr_ae
    filter_upwards [jacPull_ae F hf hJ u] with z hz
    change ‖jacPull F hf hJ u z‖^2 = _
    rw [hz,jacNorm F hJ]

def coordinateUnitary : H ≃ₗᵢ[ℂ] H := by
  apply LinearIsometryEquiv.ofSurjective (jacIsometry F hf hJ)
  intro u
  let g := fun w => u (F.symm w) / jacRoot F (F.symm w)
  have hr : Continuous (jacRoot F) := Complex.continuous_ofReal.comp (coordinateJacobian_diff F hf).continuous.sqrt
  have hg : StronglyMeasurable g := (Lp.stronglyMeasurable u |>.comp_measurable F.symm.continuous.measurable).div
    (hr.comp F.symm.continuous).stronglyMeasurable
  have hid z : jacRoot F z * g (F z) = u z := by
    have hne : jacRoot F z ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (hJ z)).ne'
    simp only [g,F.symm_apply_apply]; field_simp
  have hmem := (pull_mem_iff F hf hJ g hg).mpr (by simpa only [hid] using Lp.memLp u)
  refine ⟨hmem.toLp g,?_⟩
  apply Lp.ext
  have he := (coordinate_ae_iff F hf hJ (fun w => hmem.toLp g w = g w)).mpr hmem.coeFn_toLp
  filter_upwards [jacPull_ae F hf hJ (hmem.toLp g),he] with z hz hw
  exact hz.trans ((congrArg (jacRoot F z * ·) hw).trans (hid z))

theorem coordinateUnitary_apply (u : H) :
    (coordinateUnitary F hf hJ u : ℂ → ℂ) =ᵐ[volume]
      fun z => ((Real.sqrt (coordinateJacobian F z) : ℝ) : ℂ) * u (F z) := jacPull_ae F hf hJ u

theorem coordinateUnitary_graph (u v : H) :
    (∀ᵐ z ∂volume, coordinateUnitary F hf hJ v z = F z * coordinateUnitary F hf hJ u z) ↔
      ∀ᵐ w ∂volume, v w = w*u w := by
  rw [← coordinate_ae_iff F hf hJ (fun w => v w = w*u w)]
  apply Filter.eventually_congr
  filter_upwards [coordinateUnitary_apply F hf hJ u, coordinateUnitary_apply F hf hJ v] with z hu hv
  rw [hu,hv,mul_left_comm (F z)]
  exact mul_right_inj' (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (hJ z)).ne')

theorem coordinateUnitary_maximal_domain (u : H) :
    (∃ w : H, ∀ᵐ z ∂volume, w z = F z * coordinateUnitary F hf hJ u z) ↔
      ∃ v : H, ∀ᵐ z ∂volume, v z = z*u z := by
  constructor
  · rintro ⟨w,hw⟩
    obtain ⟨v,rfl⟩ := (coordinateUnitary F hf hJ).surjective w
    exact ⟨v,(coordinateUnitary_graph F hf hJ u v).mp hw⟩
  · rintro ⟨v,hv⟩
    exact ⟨_,(coordinateUnitary_graph F hf hJ u v).mpr hv⟩

end VortexGap.Fermion
