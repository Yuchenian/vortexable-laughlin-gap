import VortexGap.Geometry.PlaneAmplitudeL2
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory Filter
open scoped Topology

theorem planeAmplitude_series_summable (v : CountableOrbital) (z : ℂ) :
    Summable (fun n => v n * planePairAmplitude z (n+1)) := by
  apply Summable.of_norm
  simpa only [norm_mul, planePairAmplitudes] using
    lp.summable_mul (p := 2) (q := 2)
      (by rw [Real.holderConjugate_iff]; norm_num) v (planePairAmplitudes z)

/-- Identifies the L2 synthesis with the pointwise absolutely convergent series.
The a.e. assertion is obtained from an L2-convergent subsequence, rather than
assuming point evaluation is continuous on position L2. -/
theorem planeAmplitudeSynthesis_coe (v : CountableOrbital) :
    planeAmplitudeSynthesis v =ᵐ[planePairMeasure]
      (fun z => ∑' n, v n * planePairAmplitude z (n+1)) := by
  let f : ℕ → Lp ℂ 2 planePairMeasure := fun n => v n • planeAmplitudeL2 n
  have hs : HasSum f (planeAmplitudeSynthesis v) := planeAmplitudeSynthesis_hasSum v
  have ht := hs.tendsto_sum_nat
  obtain ⟨ns, hns, hlim⟩ := (tendstoInMeasure_of_tendsto_Lp ht).exists_seq_tendsto_ae
  have hsum : ∀ᵐ z ∂planePairMeasure, ∀ k : ℕ,
      (∑ n ∈ Finset.range k, f n) z = ∑ n ∈ Finset.range k, f n z := by
    rw [ae_all_iff]
    exact fun k => Lp.coeFn_fun_finsetSum _ _
  have hterm : ∀ᵐ z ∂planePairMeasure, ∀ n : ℕ,
      f n z = v n * planePairAmplitude z (n+1) := by
    rw [ae_all_iff]
    intro n
    filter_upwards [Lp.coeFn_smul (v n) (planeAmplitudeL2 n), planeAmplitudeL2_coe n] with z hz ha
    change (v n • planeAmplitudeL2 n) z = _
    rw [hz]
    change v n * planeAmplitudeL2 n z = _
    rw [ha]
  filter_upwards [hsum, hterm, hlim] with z hz hz' hzlim
  have ht' := ((planeAmplitude_series_summable v z).hasSum.tendsto_sum_nat).comp hns.tendsto_atTop
  apply tendsto_nhds_unique hzlim
  simpa only [Function.comp_def, hz, hz'] using ht'

theorem planeAmplitude_series_memLp (v : CountableOrbital) :
    MemLp (fun z => ∑' n, v n * planePairAmplitude z (n+1)) 2 planePairMeasure :=
  (Lp.memLp (planeAmplitudeSynthesis v)).ae_eq (planeAmplitudeSynthesis_coe v)

theorem planeAmplitude_series_integral (v : CountableOrbital) :
    (∫ z, ‖∑' n, v n * planePairAmplitude z (n+1)‖^2 ∂planePairMeasure) = ‖v‖^2 := by
  rw [← planeAmplitudeSynthesis_norm v, norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def,
    ← integral_re (L2.integrable_inner (planeAmplitudeSynthesis v) (planeAmplitudeSynthesis v))]
  apply integral_congr_ae
  filter_upwards [planeAmplitudeSynthesis_coe v] with z hz
  rw [hz]
  exact norm_sq_eq_re_inner (𝕜 := ℂ) _

end VortexGap.Fermion


