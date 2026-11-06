import VortexGap.Frame.TwoFrameOverlap
import VortexGap.Fermion.CountableOneFrame

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open VortexGap.Frame
open scoped BigOperators InnerProduct ComplexConjugate

/-- An orthonormal two-frame is an actual one-particle isometry. -/
abbrev CountableTwoFrame := TwoSpace →ₗᵢ[ℂ] CountableOrbital

def countableTwoFrameOverlap (U V : CountableTwoFrame) : Module.End ℂ TwoSpace :=
  (U.toContinuousLinearMap.adjoint.comp V.toContinuousLinearMap).toLinearMap

theorem countableTwoFrameOverlap_entry (U V : CountableTwoFrame) (i j : Fin 2) :
    countableTwoFrameOverlap U V (PiLp.single 2 j 1) i =
      inner ℂ (U (PiLp.single 2 i 1)) (V (PiLp.single 2 j 1)) := by
  have h := ContinuousLinearMap.adjoint_inner_right U.toContinuousLinearMap (PiLp.single 2 i 1) (V (PiLp.single 2 j 1))
  simpa only [countableTwoFrameOverlap, ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply, EuclideanSpace.inner_single_left, map_one, one_mul, LinearIsometry.coe_toContinuousLinearMap] using h

theorem countableFrameCompanion_expansion (U : CountableTwoFrame) (a : TwoSpace) :
    U (frameCompanion a) = (-conj (a 1)) • U (PiLp.single 2 0 1) + conj (a 0) • U (PiLp.single 2 1 1) := by
  have h : frameCompanion a = (-conj (a 1)) • PiLp.single 2 0 1 + conj (a 0) • PiLp.single 2 1 1 := by
    ext i
    fin_cases i <;> simp [frameCompanion]
  rw [h, map_add, map_smul, map_smul]

/-- A rank-one overlap coefficient matrix becomes a product of two actual CAR operators. -/
theorem countableTwoFrame_rank_term 
    (M : CountableOrbital →L[ℂ] CountableOrbital)
    (U V : CountableTwoFrame) (a b : TwoSpace) :
    countableAnnihilate (M (U (frameCompanion a))) * countableCreate (M (V (frameCompanion b))) =
      (a 0 * conj (b 0)) • (countableAnnihilate (M (U (PiLp.single 2 1 1))) * countableCreate (M (V (PiLp.single 2 1 1)))) -
      (a 0 * conj (b 1)) • (countableAnnihilate (M (U (PiLp.single 2 1 1))) * countableCreate (M (V (PiLp.single 2 0 1)))) -
      (a 1 * conj (b 0)) • (countableAnnihilate (M (U (PiLp.single 2 0 1))) * countableCreate (M (V (PiLp.single 2 1 1)))) +
      (a 1 * conj (b 1)) • (countableAnnihilate (M (U (PiLp.single 2 0 1))) * countableCreate (M (V (PiLp.single 2 0 1)))) := by
  simp only [countableFrameCompanion_expansion, map_add, map_smul, countableAnnihilate_add, countableAnnihilate_smul,
     map_neg, starRingEnd_self_apply,
    add_mul, mul_add, smul_mul_assoc, mul_smul_comm]
  module

theorem countableTwoFrame_rank_term_norm_le 
    (M : CountableOrbital →L[ℂ] CountableOrbital) (hc : ‖M‖ ≤ 1)
    (U V : CountableTwoFrame) (a b : TwoSpace) (x : CountableSpace) :
    ‖countableAnnihilate (M (U (frameCompanion a))) (countableCreate (M (V (frameCompanion b))) x)‖ ≤ ‖a‖ * ‖b‖ * ‖x‖ := by
  simpa only [U.norm_map, V.norm_map, frameCompanion_norm] using
    countableFiltered_annihilate_create_norm_le M hc (U (frameCompanion a)) (V (frameCompanion b)) x

/-- The exact Gram operator is a sum of two rank-one CAR products in any overlap basis. -/
theorem countableTwoFrame_gram_decomposition 
    (M : CountableOrbital →L[ℂ] CountableOrbital)
    (U V : CountableTwoFrame) (b : OrthonormalBasis (Fin 2) ℂ TwoSpace) :
    (countableOneFrameCreation M (U (PiLp.single 2 0 1)) (U (PiLp.single 2 1 1))).adjoint.comp
      (countableOneFrameCreation M (V (PiLp.single 2 0 1)) (V (PiLp.single 2 1 1))) =
      ∑ l, countableAnnihilate (M (U (frameCompanion (countableTwoFrameOverlap U V (b l))))) *
        countableCreate (M (V (frameCompanion (b l)))) := by
  rw [countableOneFrameCreation_gram]
  simp only [countableTwoFrame_rank_term, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_smul]
  rw [← two_matrix_expansion (countableTwoFrameOverlap U V) b 0 0,
    ← two_matrix_expansion (countableTwoFrameOverlap U V) b 0 1,
    ← two_matrix_expansion (countableTwoFrameOverlap U V) b 1 0,
    ← two_matrix_expansion (countableTwoFrameOverlap U V) b 1 1]
  simp only [countableTwoFrameOverlap_entry]

theorem countableTwoFrame_gram_basis_norm_le 
    (M : CountableOrbital →L[ℂ] CountableOrbital) (hc : ‖M‖ ≤ 1)
    (U V : CountableTwoFrame) (b : OrthonormalBasis (Fin 2) ℂ TwoSpace) (x : CountableSpace) :
    ‖((countableOneFrameCreation M (U (PiLp.single 2 0 1)) (U (PiLp.single 2 1 1))).adjoint.comp
      (countableOneFrameCreation M (V (PiLp.single 2 0 1)) (V (PiLp.single 2 1 1)))) x‖ ≤
      (∑ l, ‖countableTwoFrameOverlap U V (b l)‖) * ‖x‖ := by
  rw [countableTwoFrame_gram_decomposition M U V b, ContinuousLinearMap.sum_apply]
  calc
    _ ≤ ∑ l, ‖(countableAnnihilate (M (U (frameCompanion (countableTwoFrameOverlap U V (b l))))) *
        countableCreate (M (V (frameCompanion (b l))))) x‖ := norm_sum_le _ _
    _ ≤ ∑ l, ‖countableTwoFrameOverlap U V (b l)‖ * ‖b l‖ * ‖x‖ :=
      Finset.sum_le_sum fun l _ => by
        simpa only [ContinuousLinearMap.mul_apply] using
          countableTwoFrame_rank_term_norm_le M hc U V (countableTwoFrameOverlap U V (b l)) (b l) x
    _ = _ := by simp only [b.norm_eq_one, mul_one, Finset.sum_mul]

/-- Concrete two-frame trace-norm estimate on the complete countable-mode Fock space and every contraction M. -/
theorem countableTwoFrame_overlap_norm_le 
    (M : CountableOrbital →L[ℂ] CountableOrbital) (hc : ‖M‖ ≤ 1)
    (U V : CountableTwoFrame) :
    ‖(countableOneFrameCreation M (U (PiLp.single 2 0 1)) (U (PiLp.single 2 1 1))).adjoint ∘L
      (countableOneFrameCreation M (V (PiLp.single 2 0 1)) (V (PiLp.single 2 1 1)))‖ ≤
      traceNormTwo (countableTwoFrameOverlap U V) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (traceNormTwo_nonneg _)
  intro x
  change ‖((countableOneFrameCreation M (U (PiLp.single 2 0 1)) (U (PiLp.single 2 1 1))).adjoint.comp
    (countableOneFrameCreation M (V (PiLp.single 2 0 1)) (V (PiLp.single 2 1 1)))) x‖ ≤ _
  obtain ⟨b,hb⟩ := traceNormTwo_eq_sum_image_norm (countableTwoFrameOverlap U V)
  rw [hb]
  exact countableTwoFrame_gram_basis_norm_le M hc U V b x

end VortexGap.Fermion
