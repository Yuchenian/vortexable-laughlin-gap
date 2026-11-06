import VortexGap.Fermion.CountableOrbitalSpace

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped BigOperators InnerProduct ComplexConjugate

/-- Finite orbital synthesis into bounded operators on the full occupation Hilbert space. -/
def finiteOrbitalCreate : (ℕ →₀ ℂ) →ₗ[ℂ] (CountableSpace →L[ℂ] CountableSpace) :=
  Finsupp.linearCombination ℂ countableCreateMode

def finiteOrbitalAnnihilate (v : ℕ →₀ ℂ) : CountableSpace →L[ℂ] CountableSpace :=
  (finiteOrbitalCreate v).adjoint

theorem finiteOrbitalCreate_sum (v : ℕ →₀ ℂ) :
    finiteOrbitalCreate v = ∑ j ∈ v.support, v j • countableCreateMode j := rfl

theorem finiteOrbitalAnnihilate_sum (v : ℕ →₀ ℂ) :
    finiteOrbitalAnnihilate v = ∑ j ∈ v.support, conj (v j) • countableAnnihilateMode j := by
  simp [finiteOrbitalAnnihilate, finiteOrbitalCreate_sum, map_smulₛₗ, countableTransition_adjoint]

theorem finiteOrbitalCreate_single (j : ℕ) (z : ℂ) :
    finiteOrbitalCreate (Finsupp.single j z) = z • countableCreateMode j := by
  simp [finiteOrbitalCreate]

theorem finiteOrbitalAnnihilate_single (j : ℕ) (z : ℂ) :
    finiteOrbitalAnnihilate (Finsupp.single j z) = conj z • countableAnnihilateMode j := by
  simp [finiteOrbitalAnnihilate, finiteOrbitalCreate_single, map_smulₛₗ,
    countableTransition_adjoint]

theorem finiteOrbitalAnnihilate_add (v w : ℕ →₀ ℂ) :
    finiteOrbitalAnnihilate (v + w) = finiteOrbitalAnnihilate v + finiteOrbitalAnnihilate w := by
  simp [finiteOrbitalAnnihilate]

theorem finiteOrbitalAnnihilate_smul (z : ℂ) (v : ℕ →₀ ℂ) :
    finiteOrbitalAnnihilate (z • v) = conj z • finiteOrbitalAnnihilate v := by
  simp [finiteOrbitalAnnihilate, map_smulₛₗ]

theorem finiteOrbitalAnnihilate_adjoint (v : ℕ →₀ ℂ) :
    (finiteOrbitalAnnihilate v).adjoint = finiteOrbitalCreate v := by
  simp [finiteOrbitalAnnihilate]

theorem finiteOrbital_mode_car (i : ℕ) (w : ℕ →₀ ℂ) :
    countableAnnihilateMode i * finiteOrbitalCreate w +
      finiteOrbitalCreate w * countableAnnihilateMode i = w i • 1 := by
  calc
    _ = ∑ j ∈ w.support, w j • (if i = j then (1 : CountableSpace →L[ℂ] CountableSpace) else 0) := by
      rw [finiteOrbitalCreate_sum]
      simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      simpa only [smul_add] using
        congrArg (fun T : CountableSpace →L[ℂ] CountableSpace => w j • T) (countableMode_car i j)
    _ = w i • 1 := by
      rw [Finset.sum_eq_single i]
      · rw [if_pos rfl]
      · intro j hj hji
        rw [if_neg (Ne.symm hji)]
        ext x A
        change w j * (0 : ℂ) = 0
        exact mul_zero _
      · intro hi
        rw [if_pos rfl, Finsupp.notMem_support_iff.mp hi]
        ext x A
        change (0 : ℂ) * x A = 0
        exact zero_mul _

theorem finiteOrbital_car (v w : ℕ →₀ ℂ) :
    finiteOrbitalAnnihilate v * finiteOrbitalCreate w +
      finiteOrbitalCreate w * finiteOrbitalAnnihilate v =
        (inner ℂ (orbitalEmbed v) (orbitalEmbed w)) • 1 := by
  calc
    _ = ∑ i ∈ v.support, conj (v i) • (w i • (1 : CountableSpace →L[ℂ] CountableSpace)) := by
      rw [finiteOrbitalAnnihilate_sum]
      simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      simpa only [smul_add] using
        congrArg (fun T : CountableSpace →L[ℂ] CountableSpace => conj (v i) • T)
          (finiteOrbital_mode_car i w)
    _ = _ := by simp only [smul_smul]; rw [← Finset.sum_smul, orbitalEmbed_inner]

theorem finiteOrbital_norm_identity (v : ℕ →₀ ℂ) (x : CountableSpace) :
    ‖finiteOrbitalCreate v x‖ ^ 2 + ‖finiteOrbitalAnnihilate v x‖ ^ 2 =
      ‖orbitalEmbed v‖ ^ 2 * ‖x‖ ^ 2 := by
  have he : inner ℂ (finiteOrbitalCreate v x) (finiteOrbitalCreate v x) +
      inner ℂ (finiteOrbitalAnnihilate v x) (finiteOrbitalAnnihilate v x) =
        inner ℂ (orbitalEmbed v) (orbitalEmbed v) * inner ℂ x x := by
    calc
      _ = inner ℂ x ((finiteOrbitalAnnihilate v * finiteOrbitalCreate v +
          finiteOrbitalCreate v * finiteOrbitalAnnihilate v) x) := by
        rw [← ContinuousLinearMap.adjoint_inner_right (finiteOrbitalCreate v) x
            (finiteOrbitalCreate v x),
          ← ContinuousLinearMap.adjoint_inner_right (finiteOrbitalAnnihilate v) x
            (finiteOrbitalAnnihilate v x), finiteOrbitalAnnihilate_adjoint,
          ← inner_add_right]
        rfl
      _ = _ := by rw [finiteOrbital_car]; simp
  simp only [inner_self_eq_norm_sq_to_K] at he
  exact_mod_cast he

theorem finiteOrbitalCreate_norm_le (v : ℕ →₀ ℂ) (x : CountableSpace) :
    ‖finiteOrbitalCreate v x‖ ≤ ‖orbitalEmbed v‖ * ‖x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  have h := finiteOrbital_norm_identity v x
  nlinarith [sq_nonneg ‖finiteOrbitalAnnihilate v x‖]

theorem finiteOrbitalCreate_opNorm_le (v : ℕ →₀ ℂ) :
    ‖finiteOrbitalCreate v‖ ≤ ‖orbitalEmbed v‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  exact finiteOrbitalCreate_norm_le v

theorem finiteOrbitalAnnihilate_norm_le (v : ℕ →₀ ℂ) (x : CountableSpace) :
    ‖finiteOrbitalAnnihilate v x‖ ≤ ‖orbitalEmbed v‖ * ‖x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  have h := finiteOrbital_norm_identity v x
  nlinarith [sq_nonneg ‖finiteOrbitalCreate v x‖]

theorem finiteOrbitalAnnihilate_opNorm_le (v : ℕ →₀ ℂ) :
    ‖finiteOrbitalAnnihilate v‖ ≤ ‖orbitalEmbed v‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  exact finiteOrbitalAnnihilate_norm_le v

end VortexGap.Fermion
