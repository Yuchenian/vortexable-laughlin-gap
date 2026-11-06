import VortexGap.Geometry.BlochRotation
import OAI.Analysis.Laughlin.Spin.Haar
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.Unique
import VortexGap.Geometry.SphereBloch

noncomputable section
namespace VortexGap.Fermion
open VortexGap.Geometry OAI.Laughlin.Rotation MeasureTheory Metric
open scoped RealInnerProductSpace ComplexConjugate Matrix

def roundBloch (g : SourceSU2) : sphere (0:RoundAmbient) 1 :=
  ⟨rotationVector g,mem_sphere_zero_iff_norm.mpr (by
    have h := rotationVector_inner g g
    rw [real_inner_self_eq_norm_sq] at h
    simp at h
    nlinarith [norm_nonneg (rotationVector g)])⟩

theorem roundBloch_continuous : Continuous roundBloch := by
  apply Continuous.subtype_mk
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
  apply continuous_pi
  have hc (i : Fin 2) : Continuous (fun g : SourceSU2 => g.val i 0) :=
    (continuous_apply 0).comp ((continuous_apply i).comp continuous_subtype_val)
  intro i
  fin_cases i
  · exact Complex.continuous_re.comp ((continuous_const.mul (continuous_star.comp (hc 0))).mul (hc 1))
  · exact Complex.continuous_im.comp ((continuous_const.mul (continuous_star.comp (hc 0))).mul (hc 1))
  · exact (Complex.continuous_normSq.comp (hc 0)).sub (Complex.continuous_normSq.comp (hc 1))

theorem roundBloch_area_of_surjective (hp : Function.Surjective roundBloch) :
    sourceHaar.map roundBloch = normalizedRoundArea := by
  choose e he using rotationVector_ambient
  let R := fun k => sphereRotate (e k)
  have act (k g : SourceSU2) : R k (roundBloch g) = roundBloch (k*g) := Subtype.ext (he k g)
  let proj := fun p : SourceSU2 × SourceSU2 => (p.1, roundBloch p.2)
  have hproj : Continuous proj := continuous_fst.prodMk (roundBloch_continuous.comp continuous_snd)
  have hs : Function.Surjective proj := by
    rintro ⟨k,p⟩
    obtain ⟨g,rfl⟩ := hp p
    exact ⟨(k,g),rfl⟩
  have hR : Continuous R.uncurry := by
    apply (hproj.isClosedMap.isQuotientMap hproj hs).continuous_iff.mpr
    exact (show R.uncurry ∘ proj = fun p => roundBloch (p.1*p.2) from funext fun p => act _ _) ▸
      roundBloch_continuous.comp continuous_mul
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro F
  let f := fun k x => F (R k x)
  have h1 (k) : (∫ x, f k x ∂normalizedRoundArea) = ∫ x, F x ∂normalizedRoundArea := by
    have hm := normalizedRoundArea_rotation (e k)
    conv_rhs => rw [← hm.map_eq,integral_map hm.measurable.aemeasurable F.continuous.aestronglyMeasurable]
  let : sourceHaar.IsMulRightInvariant := ⟨fun g => by
    let : IsProbabilityMeasure (sourceHaar.map (· * g)) := Measure.isProbabilityMeasure_map_iff (by fun_prop) |>.mpr inferInstance
    exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _⟩
  have h2 (x) : (∫ k, f k x ∂sourceHaar) = ∫ k, F (roundBloch k) ∂sourceHaar := by
    obtain ⟨g,rfl⟩ := hp x
    simpa only [f,act] using integral_mul_right_eq_self (μ := sourceHaar) (fun k => F (roundBloch k)) g
  have hc : Continuous f.uncurry := F.continuous.comp hR
  have ht := integral_integral_swap_of_hasCompactSupport (μ := sourceHaar) (ν := normalizedRoundArea)
    hc (HasCompactSupport.of_compactSpace _)
  simp_rw [h1,h2] at ht
  rw [integral_map roundBloch_continuous.measurable.aemeasurable F.continuous.aestronglyMeasurable]
  simpa using ht.symm

/-- Exact coordinate bridge to the codomain of sphereBloch_surjective. -/
theorem roundBloch_area_of_cartesian_lifts
    (p : SourceSU2 → {a : ℂ × ℝ // Complex.normSq a.1 + a.2^2 = 1})
    (hxy : ∀ g, (p g).val.1 = 2*conj (g.val 0 0)*g.val 1 0)
    (hz : ∀ g, (p g).val.2 = Complex.normSq (g.val 0 0)-Complex.normSq (g.val 1 0))
    (hp : Function.Surjective p) :
    sourceHaar.map roundBloch = normalizedRoundArea := by
  apply roundBloch_area_of_surjective
  intro x
  let w : ℂ := ⟨x.val 0,x.val 1⟩
  have hn := mem_sphere_zero_iff_norm.mp x.property
  have hu : Complex.normSq w + (x.val 2)^2 = 1 := by
    have h := real_inner_self_eq_norm_sq x.val
    rw [hn] at h
    rw [PiLp.inner_apply,Fin.sum_univ_three] at h
    simp only [RCLike.inner_apply, conj_trivial] at h
    simp [w,Complex.normSq_apply]
    nlinarith
  obtain ⟨g,hg⟩ := hp ⟨(w,x.val 2),hu⟩
  have h := (hxy g).symm.trans (congrArg (fun y => y.val.1) hg)
  have v := (hz g).symm.trans (congrArg (fun y => y.val.2) hg)
  refine ⟨g,Subtype.ext ?_⟩
  ext i
  fin_cases i
  · exact congrArg Complex.re h
  · exact congrArg Complex.im h
  · exact v

end VortexGap.Fermion
end

namespace VortexGap.Fermion
open MeasureTheory OAI.Laughlin.Rotation VortexGap.Geometry

/-- The physical Bloch map pushes normalized SU(2) Haar measure to round area divided by 4π. -/
theorem sphereBloch_round_area :
    sourceHaar.map roundBloch = normalizedRoundArea :=
  roundBloch_area_of_cartesian_lifts sphereBloch (fun _ => rfl) (fun _ => rfl)
    sphereBloch_surjective

end VortexGap.Fermion
