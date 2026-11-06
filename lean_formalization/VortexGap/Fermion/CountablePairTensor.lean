import VortexGap.Fermion.CountablePairAmplification

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped InnerProduct ComplexConjugate

/-- A concrete elementary tensor in the completed pair-output Hilbert sum. -/
def countablePairTensor (p : CountablePairSpace) (x : CountableSpace) : CountablePairStackSpace :=
  ⟨fun a => p a • x, ((lp.memℓp p).norm.const_mul ‖x‖).mono fun a => by
    simp only [norm_smul, mul_comm]; exact le_rfl⟩

theorem countablePairTensor_apply (p : CountablePairSpace) (x : CountableSpace)
    (a : CountablePairIndex) : countablePairTensor p x a = p a • x := rfl

theorem countablePairTensor_norm (p : CountablePairSpace) (x : CountableSpace) :
    ‖countablePairTensor p x‖ = ‖p‖ * ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [l2_norm_sq]
  simp_rw [countablePairTensor_apply, norm_smul, mul_pow]
  rw [tsum_mul_right, ← l2_norm_sq]

theorem countablePairTensor_fiber (p : CountablePairSpace) (x : CountableSpace) (A : Finset ℕ) :
    countablePairFiber (countablePairTensor p x) A = x A • p := by
  ext a
  change p a * x A = x A * p a
  exact mul_comm _ _

theorem countablePairAmplify_tensor (Q : CountablePairSpace →L[ℂ] CountablePairSpace)
    (p : CountablePairSpace) (x : CountableSpace) :
    countablePairAmplify Q (countablePairTensor p x) = countablePairTensor (Q p) x := by
  ext a A
  rw [countablePairAmplify_apply, countablePairTensor_fiber, map_smul]
  change x A * Q p a = Q p a * x A
  exact mul_comm _ _

theorem countablePairContract_coefficient (p : CountablePairSpace) (z : CountablePairStackSpace)
    (A : Finset ℕ) : countablePairContract p z A = inner ℂ p (countablePairFiber z A) := by
  rw [← countableKet_inner_left, countablePairContract_apply]
  change (innerSL ℂ (countableKet A)) (∑' a, conj (p a) • z a) = _
  rw [(innerSL ℂ (countableKet A)).map_tsum (countablePairContract_summable p z), lp.inner_eq_tsum]
  apply tsum_congr
  intro a
  change inner ℂ (countableKet A) (conj (p a) • z a) = _
  rw [inner_smul_right, countableKet_inner_left]
  simp only [RCLike.inner_apply, countablePairFiber_apply, mul_comm]

theorem countablePairTensor_inner_contract (p : CountablePairSpace) (x : CountableSpace)
    (z : CountablePairStackSpace) :
    inner ℂ (countablePairTensor p x) z = inner ℂ x (countablePairContract p z) := by
  rw [countablePairContract_apply]
  change _ = (innerSL ℂ x) (∑' a, conj (p a) • z a)
  rw [(innerSL ℂ x).map_tsum (countablePairContract_summable p z), lp.inner_eq_tsum]
  apply tsum_congr
  intro a
  change inner ℂ (p a • x) (z a) = inner ℂ x (conj (p a) • z a)
  rw [inner_smul_left, inner_smul_right]

theorem countablePairContract_tensor (p q : CountablePairSpace) (x : CountableSpace) :
    countablePairContract p (countablePairTensor q x) = (inner ℂ p q) • x := by
  ext A
  rw [countablePairContract_coefficient, countablePairTensor_fiber, inner_smul_right]
  change x A * inner ℂ p q = inner ℂ p q * x A
  exact mul_comm _ _

theorem countablePairTensor_inner_contract_right (p : CountablePairSpace) (x : CountableSpace)
    (z : CountablePairStackSpace) :
    inner ℂ z (countablePairTensor p x) = inner ℂ (countablePairContract p z) x := by
  have h := congrArg conj (countablePairTensor_inner_contract p x z)
  simpa only [inner_conj_symm] using h

theorem countablePairAmplify_rankOne (p q : CountablePairSpace) (z : CountablePairStackSpace) :
    countablePairAmplify (InnerProductSpace.rankOne ℂ p q) z =
      countablePairTensor p (countablePairContract q z) := by
  ext a A
  rw [countablePairAmplify_apply]
  change (inner ℂ q (countablePairFiber z A)) * p a = p a * countablePairContract q z A
  rw [countablePairContract_coefficient, mul_comm]

theorem countablePairStack_pairEmbedding (p : CountablePairSpace) :
    countablePairStack 2 ⟨countablePairEmbedding p, countablePairEmbedding_sector p⟩ =
      countablePairTensor p (countableKet ∅) := by
  ext a A
  change countablePairMode a (countablePairEmbedding p) A = (p a • countableKet ∅) A
  rw [countablePairMode_pairEmbedding]

theorem countablePairAmplify_opNorm_eq (Q : CountablePairSpace →L[ℂ] CountablePairSpace) :
    ‖countablePairAmplify Q‖ = ‖Q‖ := by
  apply le_antisymm (countablePairAmplify_opNorm_le Q)
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro p
  have h := (countablePairAmplify Q).le_opNorm (countablePairTensor p (countableKet ∅))
  simpa only [countablePairAmplify_tensor, countablePairTensor_norm, countableKet_norm, mul_one] using h

end VortexGap.Fermion
