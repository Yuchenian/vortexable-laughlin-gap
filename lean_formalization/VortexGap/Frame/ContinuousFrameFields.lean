import VortexGap.Frame.TwoFrameOverlap
import VortexGap.Frame.ContinuousPair

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory
open scoped ENNReal

variable {n : ℕ}
  (M : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))

theorem oneFrameCreation_add_left (u v w : EuclideanSpace ℂ (Fin n)) :
    oneFrameCreation M (u+v) w = oneFrameCreation M u w + oneFrameCreation M v w := by
  apply LinearMap.ext
  intro x
  simp only [oneFrameCreation_apply, LinearMap.add_apply, map_add, create_add]
  abel

theorem oneFrameCreation_add_right (u v w : EuclideanSpace ℂ (Fin n)) :
    oneFrameCreation M u (v+w) = oneFrameCreation M u v + oneFrameCreation M u w := by
  apply LinearMap.ext
  intro x
  simp only [oneFrameCreation_apply, LinearMap.add_apply, map_add, create_add]
  abel

theorem oneFrameCreation_smul_left (z : ℂ) (u v : EuclideanSpace ℂ (Fin n)) :
    oneFrameCreation M (z • u) v = z • oneFrameCreation M u v := by
  apply LinearMap.ext
  intro x
  simp only [oneFrameCreation_apply, map_smul, create_smul, LinearMap.smul_apply, smul_sub]

theorem oneFrameCreation_smul_right (z : ℂ) (u v : EuclideanSpace ℂ (Fin n)) :
    oneFrameCreation M u (z • v) = z • oneFrameCreation M u v := by
  apply LinearMap.ext
  intro x
  simp only [oneFrameCreation_apply, map_smul, create_smul, LinearMap.smul_apply, smul_sub]

def oneFrameCreationBilinear : EuclideanSpace ℂ (Fin n) →ₗ[ℂ]
    EuclideanSpace ℂ (Fin n) →ₗ[ℂ] (Space n →L[ℂ] OrbitalStackSpace n) where
  toFun u := {
    toFun v := LinearMap.toContinuousLinearMap (oneFrameCreation M u v)
    map_add' v w := by rw [oneFrameCreation_add_right, map_add]
    map_smul' z v := by rw [oneFrameCreation_smul_right, map_smul]; rfl }
  map_add' u v := by
    apply LinearMap.ext
    intro w
    change LinearMap.toContinuousLinearMap (oneFrameCreation M (u+v) w) =
      LinearMap.toContinuousLinearMap (oneFrameCreation M u w) +
        LinearMap.toContinuousLinearMap (oneFrameCreation M v w)
    rw [oneFrameCreation_add_left, map_add]
  map_smul' z u := by
    apply LinearMap.ext
    intro v
    change LinearMap.toContinuousLinearMap (oneFrameCreation M (z • u) v) =
      z • LinearMap.toContinuousLinearMap (oneFrameCreation M u v)
    rw [oneFrameCreation_smul_left, map_smul]

/-- The actual mixed CAR column is a continuous bilinear function of its orbitals. -/
def oneFrameCreationField : EuclideanSpace ℂ (Fin n) →L[ℂ]
    EuclideanSpace ℂ (Fin n) →L[ℂ] (Space n →L[ℂ] OrbitalStackSpace n) :=
  let e : (EuclideanSpace ℂ (Fin n) →ₗ[ℂ] (Space n →L[ℂ] OrbitalStackSpace n)) ≃ₗ[ℂ]
      (EuclideanSpace ℂ (Fin n) →L[ℂ] (Space n →L[ℂ] OrbitalStackSpace n)) :=
    LinearMap.toContinuousLinearMap
  let L : EuclideanSpace ℂ (Fin n) →ₗ[ℂ]
      (EuclideanSpace ℂ (Fin n) →L[ℂ] (Space n →L[ℂ] OrbitalStackSpace n)) :=
    e.toLinearMap.comp (oneFrameCreationBilinear M)
  { toLinearMap := L
    cont := LinearMap.continuous_of_finiteDimensional (𝕜 := ℂ)
      (E := EuclideanSpace ℂ (Fin n))
      (F' := EuclideanSpace ℂ (Fin n) →L[ℂ] (Space n →L[ℂ] OrbitalStackSpace n)) L }

theorem oneFrameCreationField_apply (u v : EuclideanSpace ℂ (Fin n)) :
    oneFrameCreationField M u v = LinearMap.toContinuousLinearMap (oneFrameCreation M u v) := rfl

def wedgePairField (n : ℕ) : EuclideanSpace ℂ (Fin n) →L[ℂ]
    EuclideanSpace ℂ (Fin n) →L[ℂ] PairSpace n :=
  (((LinearMap.toContinuousLinearMap :
    (EuclideanSpace ℂ (Fin n) →ₗ[ℂ] PairSpace n) ≃ₗ[ℂ]
    (EuclideanSpace ℂ (Fin n) →L[ℂ] PairSpace n)).toLinearMap).comp (wedgePairBilinear n)).toContinuousLinearMap

theorem wedgePairField_apply (u v : EuclideanSpace ℂ (Fin n)) :
    wedgePairField n u v = wedgePair u v := rfl

private theorem bilinear_memLp {α E F G : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (μ : Measure α) [IsFiniteMeasure μ] (L : E →L[ℂ] F →L[ℂ] G)
    (u : α → E) (v : α → F)
    (hu : AEStronglyMeasurable u μ) (hv : AEStronglyMeasurable v μ)
    (hun : ∀ a, ‖u a‖ ≤ 1) (hvn : ∀ a, ‖v a‖ ≤ 1) :
    MemLp (fun a => L (u a) (v a)) 2 μ := by
  apply MemLp.of_bound (L.aestronglyMeasurable_comp₂ hu hv) ‖L‖
  apply Filter.Eventually.of_forall
  intro a
  calc
    _ ≤ ‖L (u a)‖ * ‖v a‖ := (L (u a)).le_opNorm (v a)
    _ ≤ (‖L‖ * ‖u a‖) * ‖v a‖ := mul_le_mul_of_nonneg_right (L.le_opNorm _) (norm_nonneg _)
    _ ≤ ‖L‖ * ‖v a‖ := mul_le_mul_of_nonneg_right
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left (hun a) (norm_nonneg L))
      (norm_nonneg (v a))
    _ ≤ ‖L‖ := by simpa only [mul_one] using mul_le_mul_of_nonneg_left (hvn a) (norm_nonneg L)


variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
  (u v : α → EuclideanSpace ℂ (Fin n))
  (hu : AEStronglyMeasurable u μ) (hv : AEStronglyMeasurable v μ)
  (hun : ∀ a, ‖u a‖ ≤ 1) (hvn : ∀ a, ‖v a‖ ≤ 1)

include hu hv hun hvn in
theorem oneFrameCreation_memLp :
    MemLp (fun a => LinearMap.toContinuousLinearMap (oneFrameCreation M (u a) (v a))) 2 μ :=
  bilinear_memLp μ (oneFrameCreationField M) u v hu hv hun hvn

include hu hv hun hvn in
theorem wedgePair_memLp : MemLp (fun a => wedgePair (u a) (v a)) 2 μ :=
  bilinear_memLp μ (wedgePairField n) u v hu hv hun hvn

include hu hv hun hvn in
theorem oneFrameCreation_apply_integrable (f : Lp (Space n) 2 μ) :
    Integrable (fun a => oneFrameCreation M (u a) (v a) (f a)) μ := by
  have hR := oneFrameCreation_memLp M μ u v hu hv hun hvn
  apply (hR.norm.integrable_mul (Lp.memLp f).norm).mono'
    ((ContinuousLinearMap.id ℂ ((Space n) →L[ℂ] OrbitalStackSpace n)).aestronglyMeasurable_comp₂
      hR.aestronglyMeasurable (Lp.aestronglyMeasurable f))
  exact Filter.Eventually.of_forall fun a =>
    (LinearMap.toContinuousLinearMap (oneFrameCreation M (u a) (v a))).le_opNorm (f a)

end VortexGap.Fermion

