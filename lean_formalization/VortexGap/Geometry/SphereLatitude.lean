import OAI.Analysis.Laughlin.Spin.Haar
import OAI.Analysis.Laughlin.Spin.Torus
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic
import Mathlib.MeasureTheory.Group.Circle
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section
namespace VortexGap.Fermion
open OAI.Laughlin.Rotation MeasureTheory
open scoped ComplexConjugate Matrix

/-- Haar expectation of a test function of the horizontal Bloch coordinate and spin-up weight. -/
def spinorExpectation (F : ℂ → ℝ → ℂ) : ℂ :=
  ∫ g : SourceSU2, F (2 * conj (g.val 0 0) * g.val 1 0) (‖g.val 0 0‖^2) ∂sourceHaar

theorem spinorExpectation_azimuth (F : ℂ → ℝ → ℂ) (w : ℂ) (hw : ‖w‖=1) :
    spinorExpectation (fun v t => F (w*v) t) = spinorExpectation F := by
  obtain ⟨u,hu⟩ := IsAlgClosed.exists_pow_nat_eq w (n := 2) (by decide)
  have hn := congrArg norm hu
  rw [norm_pow,hw] at hn
  have hz : ‖conj u‖=1 := by rw [Complex.norm_conj]; nlinarith [norm_nonneg u]
  let s := sourceTorus (conj u) hz
  have he (g : SourceSU2) (i : Fin 2) :
      (s*g).val i 0 = (if i=0 then conj u else u) * g.val i 0 := by
    change (Matrix.diagonal (fun j : Fin 2 => if j=0 then conj u else star (conj u)) * g.val) i 0 = _
    simp [Matrix.diagonal_mul]
  have ha (g : SourceSU2) : 2*conj ((s*g).val 0 0)*(s*g).val 1 0 =
      w*(2*conj (g.val 0 0)*g.val 1 0) := by
    simp [he, ← hu]; ring
  have hb (g : SourceSU2) : ‖(s*g).val 0 0‖^2 = ‖g.val 0 0‖^2 := by simp [he,mul_pow,hn]
  unfold spinorExpectation
  have hh := integral_mul_left_eq_self (μ := sourceHaar)
    (fun g : SourceSU2 => F (2*conj (g.val 0 0)*g.val 1 0) (‖g.val 0 0‖^2)) s
  convert hh using 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun g => (congrArg₂ F (ha g) (hb g)).symm

/-- Positive azimuthal harmonics average to zero even with arbitrary radial weighting. -/
theorem spinorExpectation_mode (n : ℕ) (hn : 0<n) (F : ℝ → ℂ) :
    spinorExpectation (fun v t => v^n * F t) = 0 := by
  obtain ⟨w,hw⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : ℂ) hn
  have hp := congrArg norm hw
  rw [norm_pow,norm_neg,norm_one] at hp
  have hu : ‖w‖=1 := by
    by_contra h
    rcases lt_or_gt_of_ne h with h|h
    · exact (ne_of_lt (pow_lt_one₀ (norm_nonneg _) h hn.ne')) hp
    · exact (ne_of_gt (one_lt_pow₀ h hn.ne')) hp
  have h := spinorExpectation_azimuth (fun v t => v^n * F t) w hu
  simp only [mul_pow,hw,one_mul,neg_mul,spinorExpectation,integral_neg] at h
  unfold spinorExpectation
  simp only [mul_pow]
  linear_combination -h/2

theorem spinorExpectation_quadrupole :
    spinorExpectation (fun v t => v^2 * (t : ℂ)) = 0 :=
  spinorExpectation_mode 2 (by decide) _

end VortexGap.Fermion
end

noncomputable section
namespace VortexGap.Fermion
open OAI.Laughlin.Rotation MeasureTheory TopologicalSpace
open scoped ComplexConjugate

def longitudeMeasure : Measure Circle := Measure.haarMeasure (⊤ : PositiveCompacts Circle)
instance longitudeHaar : Measure.IsHaarMeasure longitudeMeasure := inferInstanceAs
  (Measure.IsHaarMeasure (Measure.haarMeasure (⊤ : PositiveCompacts Circle)))
instance longitudeProbability : IsProbabilityMeasure longitudeMeasure where
  measure_univ := by simpa [longitudeMeasure] using
    (Measure.haarMeasure_self (K₀ := (⊤ : PositiveCompacts Circle)))

def longitudeAverage (F : ℂ → ℝ → ℂ) (r : ℂ) (t : ℝ) :=
  ∫ z : Circle, F ((z:ℂ)*r) t ∂longitudeMeasure

theorem longitudeAverage_radius (F : ℂ → ℝ → ℂ) (v : ℂ) (t : ℝ) :
    longitudeAverage F v t = longitudeAverage F (‖v‖ : ℂ) t := by
  by_cases hv : v=0
  · simp [hv]
  let u : Circle := ⟨v/(‖v‖ : ℂ), mem_sphere_zero_iff_norm.mpr (by simp [norm_ne_zero_iff.mpr hv])⟩
  have hu : (u:ℂ)*(‖v‖ : ℂ)=v := div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hv))
  unfold longitudeAverage
  simpa only [Circle.coe_mul,mul_assoc,hu] using
    (integral_mul_right_eq_self (μ := longitudeMeasure) (fun z : Circle => F ((z:ℂ)*(‖v‖ : ℂ)) t) u)

theorem spinorExpectation_latitude (F : ℂ → ℝ → ℂ) (hF : Continuous (Function.uncurry F)) :
    spinorExpectation F = spinorExpectation (fun v t => longitudeAverage F (‖v‖ : ℂ) t) := by
  let f := fun (w : Circle) (g : SourceSU2) =>
    F ((w:ℂ)*(2*conj (g.val 0 0)*g.val 1 0)) (‖g.val 0 0‖^2)
  have he (i : Fin 2) : Continuous (fun g : SourceSU2 => g.val i 0) :=
    (continuous_apply 0).comp ((continuous_apply i).comp continuous_subtype_val)
  have hc : Continuous (Function.uncurry f) := by
    apply hF.comp (f := fun p : Circle × SourceSU2 => ((p.1:ℂ)*(2*conj (p.2.val 0 0)*p.2.val 1 0), ‖p.2.val 0 0‖^2))
    apply Continuous.prodMk
    · exact (continuous_subtype_val.comp continuous_fst).mul
        ((continuous_const.mul (continuous_star.comp ((he 0).comp continuous_snd))).mul ((he 1).comp continuous_snd))
    · exact (((he 0).comp continuous_snd).norm.pow 2)
  have hi (w : Circle) : (∫ g, f w g ∂sourceHaar) = spinorExpectation F :=
    spinorExpectation_azimuth F w w.norm_coe
  have hs := integral_integral_swap_of_hasCompactSupport (μ := longitudeMeasure) (ν := sourceHaar)
    hc (HasCompactSupport.of_compactSpace _)
  rw [show (fun w => ∫ g, f w g ∂sourceHaar) = fun _ => spinorExpectation F from funext hi,integral_const] at hs
  simp only [probReal_univ,one_smul] at hs
  exact hs.trans (integral_congr_ae (Filter.Eventually.of_forall fun g => longitudeAverage_radius F _ _))

theorem spinor_horizontal_radius (g : SourceSU2) :
    ‖2*conj (g.val 0 0)*g.val 1 0‖ = 2*Real.sqrt ((‖g.val 0 0‖^2)*(1-‖g.val 0 0‖^2)) := by
  have he := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.mp g.property.1) 0) 0
  have hu : Complex.normSq (g.val 0 0) + Complex.normSq (g.val 1 0) = 1 := by
    simpa [Matrix.mul_apply,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply,
      Complex.mul_conj,Fin.sum_univ_two,mul_comm] using congrArg Complex.re he
  simp only [Complex.normSq_eq_norm_sq] at hu
  rw [show 1-‖g.val 0 0‖^2 = ‖g.val 1 0‖^2 by linarith, ← mul_pow,Real.sqrt_sq (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  simp [mul_assoc]

theorem spinorExpectation_radialAverage (F : ℂ → ℝ → ℂ) (hF : Continuous (Function.uncurry F)) :
    spinorExpectation F = ∫ g : SourceSU2,
      (let t := ‖g.val 0 0‖^2
       longitudeAverage F ((2*Real.sqrt (t*(1-t)) : ℝ) : ℂ) t) ∂sourceHaar := by
  rw [spinorExpectation_latitude F hF]
  unfold spinorExpectation
  simp_rw [spinor_horizontal_radius]

theorem radialLongitudeAverage_continuous (F : ℂ → ℝ → ℂ) (hF : Continuous (Function.uncurry F)) :
    Continuous (fun t : ℝ => longitudeAverage F ((2*Real.sqrt (t*(1-t)) : ℝ) : ℂ) t) := by
  let f := fun (t : ℝ) (z : Circle) => F ((z:ℂ)*((2*Real.sqrt (t*(1-t)) : ℝ) : ℂ)) t
  have hc : Continuous f.uncurry := by
    apply hF.comp (f := fun p : ℝ × Circle => ((p.2:ℂ)*((2*Real.sqrt (p.1*(1-p.1)) : ℝ) : ℂ),p.1))
    fun_prop
  simpa [longitudeAverage,f] using continuous_parametric_integral_of_continuous
    (μ := longitudeMeasure) hc (isCompact_univ : IsCompact (Set.univ : Set Circle))

end VortexGap.Fermion
end
