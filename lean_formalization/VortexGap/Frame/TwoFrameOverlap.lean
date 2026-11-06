import VortexGap.Frame.TwoFrame
import VortexGap.Frame.TraceTwo

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open VortexGap.Frame
open scoped BigOperators InnerProduct ComplexConjugate

/-- An orthonormal two-frame is an actual one-particle isometry. -/
abbrev TwoFrame (n : ℕ) := TwoSpace →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n)

def twoFrameOverlap {n : ℕ} (U V : TwoFrame n) : Module.End ℂ TwoSpace :=
  U.toLinearMap.adjoint.comp V.toLinearMap

theorem twoFrameOverlap_entry {n : ℕ} (U V : TwoFrame n) (i j : Fin 2) :
    twoFrameOverlap U V (PiLp.single 2 j 1) i =
      inner ℂ (U (PiLp.single 2 i 1)) (V (PiLp.single 2 j 1)) := by
  have h := LinearMap.adjoint_inner_right U.toLinearMap (PiLp.single 2 i 1) (V (PiLp.single 2 j 1))
  simpa only [twoFrameOverlap, LinearMap.comp_apply, EuclideanSpace.inner_single_left, map_one, one_mul, LinearIsometry.coe_toLinearMap] using h

/-- Conjugate orthogonal companion, including the orientation used by the CAR Gram formula. -/
def frameCompanion (a : TwoSpace) : TwoSpace := WithLp.toLp 2 ![-conj (a 1), conj (a 0)]

theorem frameCompanion_norm (a : TwoSpace) : ‖frameCompanion a‖ = ‖a‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, frameCompanion, add_comm]

theorem frameCompanion_expansion {n : ℕ} (U : TwoFrame n) (a : TwoSpace) :
    U (frameCompanion a) = (-conj (a 1)) • U (PiLp.single 2 0 1) + conj (a 0) • U (PiLp.single 2 1 1) := by
  have h : frameCompanion a = (-conj (a 1)) • PiLp.single 2 0 1 + conj (a 0) • PiLp.single 2 1 1 := by
    ext i
    fin_cases i <;> simp [frameCompanion]
  rw [h, map_add, map_smul, map_smul]

/-- A rank-one overlap coefficient matrix becomes a product of two actual CAR operators. -/
theorem twoFrame_rank_term {n : ℕ}
    (M : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (U V : TwoFrame n) (a b : TwoSpace) :
    annihilate (M (U (frameCompanion a))) * create (M (V (frameCompanion b))) =
      (a 0 * conj (b 0)) • (annihilate (M (U (PiLp.single 2 1 1))) * create (M (V (PiLp.single 2 1 1)))) -
      (a 0 * conj (b 1)) • (annihilate (M (U (PiLp.single 2 1 1))) * create (M (V (PiLp.single 2 0 1)))) -
      (a 1 * conj (b 0)) • (annihilate (M (U (PiLp.single 2 0 1))) * create (M (V (PiLp.single 2 1 1)))) +
      (a 1 * conj (b 1)) • (annihilate (M (U (PiLp.single 2 0 1))) * create (M (V (PiLp.single 2 0 1)))) := by
  simp only [frameCompanion_expansion, map_add, map_smul, annihilate_add, annihilate_smul,
    create_add, create_smul, map_neg, starRingEnd_self_apply,
    add_mul, mul_add, smul_mul_assoc, mul_smul_comm]
  module

theorem twoFrame_rank_term_norm_le {n : ℕ}
    (M : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) (hc : ‖M‖ ≤ 1)
    (U V : TwoFrame n) (a b : TwoSpace) (x : Space n) :
    ‖annihilate (M (U (frameCompanion a))) (create (M (V (frameCompanion b))) x)‖ ≤ ‖a‖ * ‖b‖ * ‖x‖ := by
  simpa only [U.norm_map, V.norm_map, frameCompanion_norm] using
    filtered_annihilate_create_norm_le M hc (U (frameCompanion a)) (V (frameCompanion b)) x

/-- The exact Gram operator is a sum of two rank-one CAR products in any overlap basis. -/
theorem twoFrame_gram_decomposition {n : ℕ}
    (M : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (U V : TwoFrame n) (b : OrthonormalBasis (Fin 2) ℂ TwoSpace) :
    (oneFrameCreation M (U (PiLp.single 2 0 1)) (U (PiLp.single 2 1 1))).adjoint.comp
      (oneFrameCreation M (V (PiLp.single 2 0 1)) (V (PiLp.single 2 1 1))) =
      ∑ l, annihilate (M (U (frameCompanion (twoFrameOverlap U V (b l))))) *
        create (M (V (frameCompanion (b l)))) := by
  rw [oneFrameCreation_gram]
  simp only [twoFrame_rank_term, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_smul]
  rw [← two_matrix_expansion (twoFrameOverlap U V) b 0 0,
    ← two_matrix_expansion (twoFrameOverlap U V) b 0 1,
    ← two_matrix_expansion (twoFrameOverlap U V) b 1 0,
    ← two_matrix_expansion (twoFrameOverlap U V) b 1 1]
  simp only [twoFrameOverlap_entry]

theorem twoFrame_gram_basis_norm_le {n : ℕ}
    (M : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) (hc : ‖M‖ ≤ 1)
    (U V : TwoFrame n) (b : OrthonormalBasis (Fin 2) ℂ TwoSpace) (x : Space n) :
    ‖((oneFrameCreation M (U (PiLp.single 2 0 1)) (U (PiLp.single 2 1 1))).adjoint.comp
      (oneFrameCreation M (V (PiLp.single 2 0 1)) (V (PiLp.single 2 1 1)))) x‖ ≤
      (∑ l, ‖twoFrameOverlap U V (b l)‖) * ‖x‖ := by
  rw [twoFrame_gram_decomposition M U V b, LinearMap.sum_apply]
  calc
    _ ≤ ∑ l, ‖(annihilate (M (U (frameCompanion (twoFrameOverlap U V (b l))))) *
        create (M (V (frameCompanion (b l))))) x‖ := norm_sum_le _ _
    _ ≤ ∑ l, ‖twoFrameOverlap U V (b l)‖ * ‖b l‖ * ‖x‖ :=
      Finset.sum_le_sum fun l _ => twoFrame_rank_term_norm_le M hc U V _ _ x
    _ = _ := by simp only [b.norm_eq_one, mul_one, Finset.sum_mul]

/-- Concrete two-frame trace-norm estimate for every finite mode count and every contraction M. -/
theorem twoFrame_overlap_norm_le {n : ℕ}
    (M : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) (hc : ‖M‖ ≤ 1)
    (U V : TwoFrame n) :
    ‖(oneFrameCreation M (U (PiLp.single 2 0 1)) (U (PiLp.single 2 1 1))).toContinuousLinearMap.adjoint ∘L
      (oneFrameCreation M (V (PiLp.single 2 0 1)) (V (PiLp.single 2 1 1))).toContinuousLinearMap‖ ≤
      traceNormTwo (twoFrameOverlap U V) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (traceNormTwo_nonneg _)
  intro x
  change ‖((oneFrameCreation M (U (PiLp.single 2 0 1)) (U (PiLp.single 2 1 1))).adjoint.comp
    (oneFrameCreation M (V (PiLp.single 2 0 1)) (V (PiLp.single 2 1 1)))) x‖ ≤ _
  obtain ⟨b,hb⟩ := traceNormTwo_eq_sum_image_norm (twoFrameOverlap U V)
  rw [hb]
  exact twoFrame_gram_basis_norm_le M hc U V b x

end VortexGap.Fermion
