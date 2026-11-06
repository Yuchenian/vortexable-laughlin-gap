import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Tactic

noncomputable section
namespace VortexGap.Geometry
open MeasureTheory Metric Set
open scoped Pointwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

def sphereRotate (e : E ≃ₗᵢ[ℝ] E) (p : sphere (0:E) 1) : sphere (0:E) 1 :=
  ⟨e p,mem_sphere_zero_iff_norm.mpr (by simpa using mem_sphere_zero_iff_norm.mp p.property)⟩

theorem sphereRotate_preserves_area (e : E ≃ₗᵢ[ℝ] E) :
    MeasurePreserving (sphereRotate e) (volume : Measure E).toSphere volume.toSphere := by
  have hc : Continuous (sphereRotate e) := Continuous.subtype_mk (e.continuous.comp continuous_subtype_val) _
  refine ⟨hc.measurable,?_⟩
  ext s hs
  rw [Measure.map_apply hc.measurable hs,Measure.toSphere_apply' _ (hc.measurable hs),Measure.toSphere_apply' _ hs]
  congr 1
  let cone (s : Set (sphere (0:E) 1)) := Ioo (0:ℝ) 1 • (Subtype.val '' s)
  have he : cone (sphereRotate e ⁻¹' s) = e ⁻¹' cone s := by
    ext x
    constructor
    · rintro ⟨r,hr,_,⟨p,hp,rfl⟩,rfl⟩
      exact ⟨r,hr,e p,⟨sphereRotate e p,hp,rfl⟩,(e.map_smul r (p:E)).symm⟩
    · rintro ⟨r,hr,_,⟨p,hp,rfl⟩,hx⟩
      refine ⟨r,hr,e.symm p,⟨sphereRotate e.symm p,?_,rfl⟩,?_⟩
      · change sphereRotate e (sphereRotate e.symm p) ∈ s
        rwa [show sphereRotate e (sphereRotate e.symm p) = p from Subtype.ext (e.apply_symm_apply _)]
      · apply e.injective
        simpa using hx
  change volume (cone _) = volume (cone s)
  rw [he]
  exact e.measurePreserving.measure_preimage_emb e.toHomeomorph.measurableEmbedding _

abbrev RoundAmbient := EuclideanSpace ℝ (Fin 3)

theorem roundArea_total :
    (volume : Measure RoundAmbient).toSphere univ = ENNReal.ofReal (4*Real.pi) := by
  rw [Measure.toSphere_apply_univ]
  simp only [finrank_euclideanSpace_fin, Nat.cast_ofNat, EuclideanSpace.volume_ball_fin_three,
    ENNReal.ofReal_one, one_pow,one_mul]
  rw [show (3 : ENNReal) = ENNReal.ofReal 3 by norm_num, ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  ring

def normalizedRoundArea : Measure (sphere (0 : RoundAmbient) 1) :=
  (ENNReal.ofReal (4*Real.pi))⁻¹ • (volume : Measure RoundAmbient).toSphere

instance normalizedRoundAreaProbability : IsProbabilityMeasure normalizedRoundArea where
  measure_univ := by
    rw [normalizedRoundArea,Measure.smul_apply,roundArea_total]
    exact ENNReal.inv_mul_cancel (by positivity) ENNReal.ofReal_ne_top

theorem normalizedRoundArea_rotation (e : RoundAmbient ≃ₗᵢ[ℝ] RoundAmbient) :
    MeasurePreserving (sphereRotate e) normalizedRoundArea normalizedRoundArea := by
  have h := sphereRotate_preserves_area e
  exact ⟨h.measurable,by rw [normalizedRoundArea,Measure.map_smul,h.map_eq] <;> exact h.measurable.aemeasurable⟩

end VortexGap.Geometry
end
