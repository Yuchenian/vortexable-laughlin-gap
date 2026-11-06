import VortexGap.Fermion.CountableFieldParseval
import VortexGap.Physical.PlaneZeroAmplitudes
import Mathlib.MeasureTheory.Integral.Pi

noncomputable section
namespace VortexGap.Fermion
open MeasureTheory
open scoped ENNReal
abbrev planeConfigMeasure (N : ℕ) := Measure.pi (fun _ : Fin N => (volume : Measure ℂ))

theorem planeOrdered_continuous (field : ℂ → CountableSpace →L[ℂ] CountableSpace) (hc : Continuous field)
    (N : ℕ) : Continuous (fun z : Fin N → ℂ => planeOrderedAmplitude field (List.ofFn z)) := by
  induction N with
  | zero => simpa only [List.ofFn_zero,planeOrderedAmplitude] using continuous_const
  | succ n ih =>
    simp only [List.ofFn_succ,planeOrderedAmplitude]
    exact (ih.comp (continuous_pi fun i => continuous_apply i.succ)).clm_comp (hc.comp (continuous_apply 0))

namespace OrderedField
variable (field : ℂ → CountableSpace →L[ℂ] CountableSpace) (hc : Continuous field)
  (lower : ∀ {n} z x, x ∈ countableSector (n+1) → field z x ∈ countableSector n)
  (mem : ∀ {n} x, x ∈ countableSector n → MemLp (fun z => field z x) 2 volume)
  (number : ∀ {n} x, x ∈ countableSector n → (∫ z, ‖field z x‖^2) = (n:ℝ)*‖x‖^2)
include field hc lower mem number
theorem planeOrdered_lintegral (N : ℕ) (x : CountableSpace)
    (hx : x ∈ countableSector N) :
    (∫⁻ z, ENNReal.ofReal (‖planeOrderedAmplitude field (List.ofFn z) x‖^2) ∂planeConfigMeasure N) =
      (N.factorial:ℝ≥0∞)*ENNReal.ofReal (‖x‖^2) := by
  induction N generalizing x with
  | zero =>
    have hn := countableSpace_norm_sq x
    rw [tsum_eq_single ∅ (fun A hA => by rw [hx A (by simpa using hA)]; norm_num)] at hn
    simp [List.ofFn_zero,planeOrderedAmplitude,planeConfigMeasure,Measure.pi_empty_univ,hn]; rfl
  | succ n ih =>
    let F := fun z : Fin (n+1) → ℂ => ENNReal.ofReal (‖planeOrderedAmplitude field (List.ofFn z) x‖^2)
    have hF : Measurable F := ENNReal.measurable_ofReal.comp
      (((planeOrdered_continuous field hc _).clm_apply continuous_const).norm.pow 2).measurable
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℂ) 0
    have hm := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => (volume : Measure ℂ)) 0).symm
    change (∫⁻ z, F z ∂_) = _
    rw [← hm.lintegral_comp hF,lintegral_prod (fun p => F (e.symm p)) (hF.comp hm.measurable).aemeasurable]
    have step (z : ℂ) : (∫⁻ t, F (e.symm (z,t)) ∂planeConfigMeasure n) =
        (n.factorial:ℝ≥0∞)*ENNReal.ofReal (‖field z x‖^2) := by
      have hcons (t : Fin n → ℂ) : e.symm (z,t) = Fin.cons z t := by
        simp [e,MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv]
      simp only [hcons,F,List.ofFn_cons,planeOrderedAmplitude,ContinuousLinearMap.comp_apply]
      exact ih (field z x) (lower z x hx)
    change (∫⁻ z, (∫⁻ t, F (e.symm (z,t)) ∂planeConfigMeasure n)) = _
    simp_rw [step]
    rw [lintegral_const_mul' _ _ (by simp)]
    have hL := mem x hx
    have hi := (memLp_two_iff_integrable_sq_norm (hc.clm_apply (g := fun _ => x) continuous_const).aestronglyMeasurable).mp hL
    rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun _ => sq_nonneg _),
      number x hx, ENNReal.ofReal_mul (by positivity),Nat.factorial_succ]
    push_cast
    simp [ENNReal.ofReal_add (Nat.cast_nonneg _) zero_le_one,mul_comm,mul_assoc]

theorem planeConfiguration_lintegral {N : ℕ} (x : countableSector N) :
    (∫⁻ z, ENNReal.ofReal (‖planeConfigurationAmplitude field x z‖^2) ∂planeConfigMeasure N) =
      ENNReal.ofReal (‖x‖^2) := by
  have h (z : Fin N → ℂ) : ENNReal.ofReal (‖planeConfigurationAmplitude field x z‖^2) =
      (N.factorial:ℝ≥0∞)⁻¹ * ENNReal.ofReal (‖planeOrderedAmplitude field (List.ofFn z) x‖^2) := by
    simp only [planeConfigurationAmplitude,norm_mul,mul_pow,norm_inv,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _),inv_pow,Real.sq_sqrt (Nat.cast_nonneg _),
      ENNReal.ofReal_mul (inv_nonneg.mpr (Nat.cast_nonneg _)),ENNReal.ofReal_inv_of_pos (by positivity : 0<(N.factorial:ℝ)),
      ENNReal.ofReal_natCast]
  simp_rw [h]
  rw [lintegral_const_mul' _ _ (by finiteness),planeOrdered_lintegral field hc lower mem number N x x.property,← mul_assoc,
    ENNReal.inv_mul_cancel (by exact_mod_cast Nat.factorial_ne_zero N) (by finiteness),one_mul]
  rfl

theorem planeConfiguration_memLp {N : ℕ} (x : countableSector N) :
    MemLp (planeConfigurationAmplitude field x) 2 (planeConfigMeasure N) := by
  have hcAmp : Continuous (planeConfigurationAmplitude field x) :=
    continuous_const.mul ((planeOrdered_continuous _ (hc) N).clm_apply continuous_const)
  apply (memLp_two_iff_integrable_sq_norm hcAmp.aestronglyMeasurable).mpr
  refine ⟨(hcAmp.norm.pow 2).aestronglyMeasurable,?_⟩
  change (∫⁻ z, ‖‖planeConfigurationAmplitude field x z‖^2‖ₑ ∂planeConfigMeasure N) < ⊤
  simp_rw [Real.enorm_of_nonneg (sq_nonneg _)]
  rw [planeConfiguration_lintegral field hc lower mem number]
  exact ENNReal.ofReal_lt_top

omit hc lower mem number in
def planeConfigurationRow {N : ℕ} (z : Fin N → ℂ) : countableSector N →L[ℂ] ℂ :=
  (Real.sqrt N.factorial : ℂ)⁻¹ • (planeOrderedAmplitude field (List.ofFn z)).comp (countableSector N).subtypeL

def planeReferenceConfigurationL2 (N : ℕ) :
    countableSector N →ₗᵢ[ℂ] Lp ℂ 2 (planeConfigMeasure N) where
  toLinearMap := Frame.besselAnalysisLinear _ (planeConfigurationRow field) (planeConfiguration_memLp field hc lower mem number)
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    refine (Frame.besselAnalysisLinear_norm_sq (planeConfigMeasure N) (planeConfigurationRow field) (planeConfiguration_memLp field hc lower mem number) x).trans ?_
    change (∫ z, ‖planeConfigurationAmplitude field x z‖^2 ∂planeConfigMeasure N) = ‖x‖^2
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
      ((planeConfiguration_memLp field hc lower mem number x).aestronglyMeasurable.norm.pow 2),
      planeConfiguration_lintegral field hc lower mem number x, ENNReal.toReal_ofReal (sq_nonneg _)]

theorem planeReferenceConfigurationL2_ae {N : ℕ} (x : countableSector N) :
    planeReferenceConfigurationL2 field hc lower mem number N x =ᵐ[planeConfigMeasure N]
      planeConfigurationAmplitude field x := (planeConfiguration_memLp field hc lower mem number x).coeFn_toLp

end OrderedField

theorem planeOrdered_lintegral (ell : ℝ) (hell : 0<ell) (N : ℕ) (x : CountableSpace)
    (hx : x ∈ countableSector N) :
    (∫⁻ z, ENNReal.ofReal (‖planeOrderedAmplitude (planeField ell) (List.ofFn z) x‖^2) ∂planeConfigMeasure N) =
      (N.factorial:ℝ≥0∞)*ENNReal.ofReal (‖x‖^2) :=
  OrderedField.planeOrdered_lintegral (planeField ell) (countableAnnihilate_continuous.comp (planeEvaluation_continuous ell)) (fun _ _ hx => countableAnnihilate_sector _ hx) (fun _ hx => planeField_sector_memLp ell hell _ hx) (fun _ hx => planeField_integral_number ell hell _ hx) N x hx

theorem planeConfiguration_lintegral (ell : ℝ) (hell : 0<ell) {N : ℕ} (x : countableSector N) :
    (∫⁻ z, ENNReal.ofReal (‖planeConfigurationAmplitude (planeField ell) x z‖^2) ∂planeConfigMeasure N) =
      ENNReal.ofReal (‖x‖^2) :=
  OrderedField.planeConfiguration_lintegral (planeField ell) (countableAnnihilate_continuous.comp (planeEvaluation_continuous ell)) (fun _ _ hx => countableAnnihilate_sector _ hx) (fun _ hx => planeField_sector_memLp ell hell _ hx) (fun _ hx => planeField_integral_number ell hell _ hx) x

theorem planeConfiguration_memLp (ell : ℝ) (hell : 0<ell) {N : ℕ} (x : countableSector N) :
    MemLp (planeConfigurationAmplitude (planeField ell) x) 2 (planeConfigMeasure N) :=
  OrderedField.planeConfiguration_memLp (planeField ell) (countableAnnihilate_continuous.comp (planeEvaluation_continuous ell)) (fun _ _ hx => countableAnnihilate_sector _ hx) (fun _ hx => planeField_sector_memLp ell hell _ hx) (fun _ hx => planeField_integral_number ell hell _ hx) x

def planeConfigurationRow (ell : ℝ) {N : ℕ} (z : Fin N → ℂ) : countableSector N →L[ℂ] ℂ :=
  OrderedField.planeConfigurationRow (planeField ell) z

def planeReferenceConfigurationL2 (ell : ℝ) (hell : 0<ell) (N : ℕ) :
    countableSector N →ₗᵢ[ℂ] Lp ℂ 2 (planeConfigMeasure N) :=
  OrderedField.planeReferenceConfigurationL2 (planeField ell) (countableAnnihilate_continuous.comp (planeEvaluation_continuous ell)) (fun _ _ hx => countableAnnihilate_sector _ hx) (fun _ hx => planeField_sector_memLp ell hell _ hx) (fun _ hx => planeField_integral_number ell hell _ hx) N

theorem planeReferenceConfigurationL2_ae (ell : ℝ) (hell : 0<ell) {N : ℕ} (x : countableSector N) :
    planeReferenceConfigurationL2 ell hell N x =ᵐ[planeConfigMeasure N]
      planeConfigurationAmplitude (planeField ell) x :=
  OrderedField.planeReferenceConfigurationL2_ae (planeField ell) (countableAnnihilate_continuous.comp (planeEvaluation_continuous ell)) (fun _ _ hx => countableAnnihilate_sector _ hx) (fun _ hx => planeField_sector_memLp ell hell _ hx) (fun _ hx => planeField_integral_number ell hell _ hx) x

end VortexGap.Fermion
end
