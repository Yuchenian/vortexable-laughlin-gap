import VortexGap.Fermion.CountablePairTensor

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped InnerProduct ComplexOrder

/-- The bounded pair lift on the complete fixed-N sector, from actual CAR analysis. -/
def countablePairLift (N : ℕ) (Q : CountablePairSpace →L[ℂ] CountablePairSpace) :
    countableSector N →L[ℂ] countableSector N :=
  (countablePairStack N).adjoint.comp ((countablePairAmplify Q).comp (countablePairStack N))

theorem countablePairLift_gram {N : ℕ} (Q : CountablePairSpace →L[ℂ] CountablePairSpace)
    (x y : countableSector N) :
    inner ℂ x (countablePairLift N Q y) =
      inner ℂ (countablePairStack N x) (countablePairAmplify Q (countablePairStack N y)) := by
  change inner ℂ x ((countablePairStack N).adjoint
    (countablePairAmplify Q (countablePairStack N y))) = _
  exact ContinuousLinearMap.adjoint_inner_right (countablePairStack N) x
    (countablePairAmplify Q (countablePairStack N y))

theorem countablePairLift_norm_le {N : ℕ} (Q : CountablePairSpace →L[ℂ] CountablePairSpace)
    (x : countableSector N) :
    ‖countablePairLift N Q x‖ ≤ (N.choose 2 : ℝ) * ‖Q‖ * ‖x‖ := by
  change ‖(countablePairStack N).adjoint (countablePairAmplify Q (countablePairStack N x))‖ ≤ _
  calc
    _ ≤ ‖(countablePairStack N).adjoint‖ * ‖countablePairAmplify Q (countablePairStack N x)‖ :=
      (countablePairStack N).adjoint.le_opNorm _
    _ ≤ ‖(countablePairStack N).adjoint‖ * (‖Q‖ * ‖countablePairStack N x‖) :=
      mul_le_mul_of_nonneg_left (countablePairAmplify_norm_le Q _) (norm_nonneg _)
    _ = Real.sqrt (N.choose 2 : ℝ) ^ 2 * ‖Q‖ * ‖x‖ := by
      rw [ContinuousLinearMap.adjoint.norm_map, countablePairStack_opNorm_eq, countablePairStack_norm]
      ring
    _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg _)]

theorem countablePairLift_opNorm_le (N : ℕ) (Q : CountablePairSpace →L[ℂ] CountablePairSpace) :
    ‖countablePairLift N Q‖ ≤ (N.choose 2 : ℝ) * ‖Q‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
    (countablePairLift_norm_le Q)

theorem countablePairLift_add (N : ℕ) (Q R : CountablePairSpace →L[ℂ] CountablePairSpace) :
    countablePairLift N (Q + R) = countablePairLift N Q + countablePairLift N R := by
  ext x
  simp only [countablePairLift, countablePairAmplify_add, ContinuousLinearMap.comp_apply,
    add_apply, map_add]

theorem countablePairLift_smul (N : ℕ) (c : ℂ) (Q : CountablePairSpace →L[ℂ] CountablePairSpace) :
    countablePairLift N (c • Q) = c • countablePairLift N Q := by
  ext x
  simp only [countablePairLift, countablePairAmplify_smul, ContinuousLinearMap.comp_apply,
    smul_apply, map_smul]

def countablePairLiftLinear (N : ℕ) :
    (CountablePairSpace →L[ℂ] CountablePairSpace) →ₗ[ℂ]
      (countableSector N →L[ℂ] countableSector N) where
  toFun := countablePairLift N
  map_add' := countablePairLift_add N
  map_smul' := countablePairLift_smul N

theorem countablePairLift_zero (N : ℕ) : countablePairLift N 0 = 0 :=
  (countablePairLiftLinear N).map_zero

theorem countablePairLift_sub (N : ℕ) (Q R : CountablePairSpace →L[ℂ] CountablePairSpace) :
    countablePairLift N (Q - R) = countablePairLift N Q - countablePairLift N R := by
  change countablePairLiftLinear N (Q - R) = countablePairLiftLinear N Q - countablePairLiftLinear N R
  exact map_sub (countablePairLiftLinear N) Q R

theorem countablePairLift_sum (N : ℕ) {ι : Type*} (s : Finset ι)
    (Q : ι → CountablePairSpace →L[ℂ] CountablePairSpace) :
    countablePairLift N (∑ i ∈ s, Q i) = ∑ i ∈ s, countablePairLift N (Q i) := by
  change countablePairLiftLinear N (∑ i ∈ s, Q i) = ∑ i ∈ s, countablePairLiftLinear N (Q i)
  exact map_sum (countablePairLiftLinear N) Q s

theorem countablePairLift_positive (N : ℕ) (Q : CountablePairSpace →L[ℂ] CountablePairSpace)
    (hQ : Q.IsPositive) : (countablePairLift N Q).IsPositive :=
  (countablePairAmplify_positive Q hQ).adjoint_conj (countablePairStack N)

theorem countablePairLift_mono (N : ℕ) {Q R : CountablePairSpace →L[ℂ] CountablePairSpace}
    (h : Q ≤ R) : countablePairLift N Q ≤ countablePairLift N R := by
  rw [ContinuousLinearMap.le_def] at h ⊢
  rw [← countablePairLift_sub]
  exact countablePairLift_positive N _ h

theorem countablePairLift_adjoint (N : ℕ) (Q : CountablePairSpace →L[ℂ] CountablePairSpace) :
    (countablePairLift N Q).adjoint = countablePairLift N Q.adjoint := by
  simp only [countablePairLift, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint, countablePairAmplify_adjoint,
    ContinuousLinearMap.comp_assoc]

theorem countablePairLift_zero_sector (Q : CountablePairSpace →L[ℂ] CountablePairSpace) :
    countablePairLift 0 Q = 0 := by
  simp [countablePairLift, countablePairStack_zero]

theorem countablePairLift_one_sector (Q : CountablePairSpace →L[ℂ] CountablePairSpace) :
    countablePairLift 1 Q = 0 := by
  simp [countablePairLift, countablePairStack_one]

theorem countablePairStack_adjoint_tensor (N : ℕ) (p : CountablePairSpace) (x : CountableSpace) :
    (countablePairStack N).adjoint (countablePairTensor p x) =
      (countablePairAnnihilate N p).adjoint x := by
  apply ext_inner_left ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_right,
    countablePairTensor_inner_contract_right]
  rfl

theorem countablePairLift_rankOne (N : ℕ) (p q : CountablePairSpace) :
    countablePairLift N (InnerProductSpace.rankOne ℂ p q) =
      (countablePairAnnihilate N p).adjoint.comp (countablePairAnnihilate N q) := by
  apply ContinuousLinearMap.ext
  intro x
  change (countablePairStack N).adjoint
    (countablePairAmplify (InnerProductSpace.rankOne ℂ p q) (countablePairStack N x)) = _
  rw [countablePairAmplify_rankOne, countablePairStack_adjoint_tensor]
  rfl

theorem countablePairStack_two_adjoint_self :
    (countablePairStack 2).adjoint.comp (countablePairStack 2) = 1 := by
  apply (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mp
  intro x
  rw [countablePairStack_norm]
  norm_num [Nat.choose]

theorem countablePairLift_pairEmbedding (Q : CountablePairSpace →L[ℂ] CountablePairSpace)
    (p : CountablePairSpace) :
    countablePairLift 2 Q ⟨countablePairEmbedding p, countablePairEmbedding_sector p⟩ =
      ⟨countablePairEmbedding (Q p), countablePairEmbedding_sector (Q p)⟩ := by
  change (countablePairStack 2).adjoint (countablePairAmplify Q
    (countablePairStack 2 ⟨countablePairEmbedding p, countablePairEmbedding_sector p⟩)) = _
  rw [countablePairStack_pairEmbedding, countablePairAmplify_tensor,
    ← countablePairStack_pairEmbedding]
  change ((countablePairStack 2).adjoint.comp (countablePairStack 2)) _ = _
  rw [countablePairStack_two_adjoint_self]
  rfl

end VortexGap.Fermion
