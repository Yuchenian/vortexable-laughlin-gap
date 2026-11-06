import VortexGap.Frame.OneEnvironment

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped BigOperators InnerProduct ComplexConjugate

theorem create_adjoint {n : ℕ} (u : EuclideanSpace ℂ (Fin n)) :
    (create u).adjoint = annihilate u := by
  rw [← annihilate_adjoint, LinearMap.adjoint_adjoint]

theorem create_norm_le {n : ℕ} (u : EuclideanSpace ℂ (Fin n)) (x : Space n) :
    ‖create u x‖ ≤ ‖u‖ * ‖x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  have h := vector_norm_identity u x
  nlinarith only [h, sq_nonneg ‖annihilate u x‖]

/-- The raw one-environment column R_U, before applying the environment defect E. -/
def oneFrameCreation {n : ℕ}
    (M : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (u v : EuclideanSpace ℂ (Fin n)) : Space n →ₗ[ℂ] OrbitalStackSpace n :=
  (orbitalProduct u).comp (create (M v)) - (orbitalProduct v).comp (create (M u))

theorem oneFrameCreation_apply {n : ℕ}
    (M : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (u v : EuclideanSpace ℂ (Fin n)) (x : Space n) :
    oneFrameCreation M u v x = orbitalProduct u (create (M v) x) - orbitalProduct v (create (M u) x) := rfl

theorem oneLossCreation_factorization {n : ℕ}
    (M : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (u v : EuclideanSpace ℂ (Fin n)) (x : Space n) :
    oneLossCreation M u v x =
      orbitalEnvironmentEmbed (orbitalAmplify (lossDefect M) (oneFrameCreation M u v x)) := by
  simp only [oneFrameCreation_apply, map_sub, orbitalAmplify_product, orbitalEnvironmentEmbed_product,
    oneLossCreation, LinearMap.sub_apply, LinearMap.comp_apply]

theorem oneFrameCreation_inner {n : ℕ}
    (M : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (u v s t : EuclideanSpace ℂ (Fin n)) (x y : Space n) :
    inner ℂ (oneFrameCreation M u v x) (oneFrameCreation M s t y) =
      inner ℂ u s * inner ℂ (create (M v) x) (create (M t) y) -
      inner ℂ u t * inner ℂ (create (M v) x) (create (M s) y) -
      inner ℂ v s * inner ℂ (create (M u) x) (create (M t) y) +
      inner ℂ v t * inner ℂ (create (M u) x) (create (M s) y) := by
  simp only [oneFrameCreation_apply, inner_sub_left, inner_sub_right, orbitalProduct_inner]
  ring

/-- The concrete operator Gram formula. No contraction or orthonormality is needed for this identity. -/
theorem oneFrameCreation_gram {n : ℕ}
    (M : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (u v s t : EuclideanSpace ℂ (Fin n)) :
    (oneFrameCreation M u v).adjoint.comp (oneFrameCreation M s t) =
      (inner ℂ u s) • (annihilate (M v) * create (M t)) -
      (inner ℂ u t) • (annihilate (M v) * create (M s)) -
      (inner ℂ v s) • (annihilate (M u) * create (M t)) +
      (inner ℂ v t) • (annihilate (M u) * create (M s)) := by
  apply LinearMap.ext
  intro y
  apply ext_inner_left ℂ
  intro x
  rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right, oneFrameCreation_inner]
  have hi (a b : EuclideanSpace ℂ (Fin n)) :
      inner ℂ (create a x) (create b y) = inner ℂ x (annihilate a (create b y)) := by
    rw [← LinearMap.adjoint_inner_right (create a) x (create b y), create_adjoint]
  simp only [hi, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    inner_add_right, inner_sub_right, inner_smul_right, Module.End.mul_apply]

theorem oneFrameCreation_change_basis {n : ℕ}
    (M : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (u v : EuclideanSpace ℂ (Fin n)) (a b c d : ℂ) :
    oneFrameCreation M (a • u + b • v) (c • u + d • v) =
      (a*d-b*c) • oneFrameCreation M u v := by
  apply LinearMap.ext
  intro x
  simp only [oneFrameCreation_apply, map_add, map_smul, create_add, create_smul,
    LinearMap.add_apply, LinearMap.smul_apply]
  module

/-- A dimension-free CAR product bound for the contraction M. -/
theorem filtered_annihilate_create_norm_le {n : ℕ}
    (M : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) (hc : ‖M‖ ≤ 1)
    (a b : EuclideanSpace ℂ (Fin n)) (x : Space n) :
    ‖annihilate (M a) (create (M b) x)‖ ≤ (‖a‖ * ‖b‖) * ‖x‖ := by
  have hm (v : EuclideanSpace ℂ (Fin n)) : ‖M v‖ ≤ ‖v‖ := by
    simpa only [one_mul] using (M.le_opNorm v).trans (mul_le_mul_of_nonneg_right hc (norm_nonneg v))
  calc
    _ ≤ ‖M a‖ * ‖create (M b) x‖ := annihilate_norm_le _ _
    _ ≤ ‖M a‖ * (‖M b‖ * ‖x‖) := mul_le_mul_of_nonneg_left (create_norm_le _ _) (norm_nonneg _)
    _ ≤ ‖a‖ * (‖b‖ * ‖x‖) := mul_le_mul (hm a)
      (mul_le_mul_of_nonneg_right (hm b) (norm_nonneg x))
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
    _ = _ := by ring

end VortexGap.Fermion
