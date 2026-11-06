import VortexGap.Fermion.NumberParity
import VortexGap.Fermion.ExteriorSquare

/-! Concrete pair-annihilation factorization and the arbitrary-N operator norm bound. -/
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped BigOperators InnerProduct ComplexConjugate

theorem sum_annihilateMode_norm_sq {n : ℕ} (x : Space n) :
    (∑ i : Fin n, ‖annihilateMode i x‖ ^ 2) = (inner ℂ x (number n x)).re := by
  rw [number_eq_sum]
  simp only [LinearMap.sum_apply, inner_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Module.End.mul_apply, ← mode_adjoint, LinearMap.adjoint_inner_right,
    inner_self_eq_norm_sq_to_K]
  simp [← Complex.ofReal_pow]

theorem sum_annihilateMode_norm_sq_of_sector {n N : ℕ} {x : Space n}
    (hx : InSector N x) :
    (∑ i : Fin n, ‖annihilateMode i x‖ ^ 2) = (N : ℝ) * ‖x‖ ^ 2 := by
  rw [sum_annihilateMode_norm_sq, number_on_sector hx, inner_smul_right,
    inner_self_eq_norm_sq_to_K]
  simp [← Complex.ofReal_pow]

theorem double_annihilation_sum {n : ℕ} (x : Space n) :
    (∑ i : Fin n, ∑ j : Fin n, ‖annihilateMode j (annihilateMode i x)‖ ^ 2) =
      2 * ∑ a : PairIndex n, ‖pairMode a x‖ ^ 2 := by
  rw [sum_split_orderedPairs (fun i j => ‖annihilateMode j (annihilateMode i x)‖ ^ 2)
    (by intro i; rw [← Module.End.mul_apply, mode_square]; simp)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  have h : annihilateMode a.val.1 (annihilateMode a.val.2 x) = -pairMode a x := by
    rw [← Module.End.mul_apply, mode_anticommute]
    rfl
  rw [h, norm_neg]
  change ‖pairMode a x‖ ^ 2 + ‖pairMode a x‖ ^ 2 = 2 * ‖pairMode a x‖ ^ 2
  ring

/-- Every unordered pair is counted once, for arbitrary mode count and particle number.
The zero- and one-particle sectors are dealt with explicitly. -/
theorem sum_pairMode_norm_sq {n N : ℕ} {x : Space n} (hx : InSector N x) :
    (∑ a : PairIndex n, ‖pairMode a x‖ ^ 2) = (N.choose 2 : ℝ) * ‖x‖ ^ 2 := by
  obtain _ | _ | N := N
  · simp [pairMode_sector_zero _ hx]
  · simp [pairMode_sector_one _ hx]
  · have hi (i : Fin n) :
        (∑ j : Fin n, ‖annihilateMode j (annihilateMode i x)‖ ^ 2) =
          ((N + 1 : ℕ) : ℝ) * ‖annihilateMode i x‖ ^ 2 :=
      sum_annihilateMode_norm_sq_of_sector (annihilateMode_sector i hx)
    have hd : (∑ i : Fin n, ∑ j : Fin n,
        ‖annihilateMode j (annihilateMode i x)‖ ^ 2) =
        ((N + 1 : ℕ) : ℝ) * ((N + 2 : ℕ) : ℝ) * ‖x‖ ^ 2 := by
      simp_rw [hi]
      rw [← Finset.mul_sum, sum_annihilateMode_norm_sq_of_sector hx]
      ring
    rw [double_annihilation_sum] at hd
    rw [Nat.cast_choose_two]
    push_cast at hd ⊢
    nlinarith

abbrev PairStackSpace (n : ℕ) := EuclideanSpace ℂ (PairIndex n × Finset (Fin n))

/-- All pair annihilation outputs, in their actual finite Hilbert direct sum. -/
def pairStack {n : ℕ} : Space n →ₗ[ℂ] PairStackSpace n where
  toFun x := WithLp.toLp 2 (fun aA => pairMode aA.1 x aA.2)
  map_add' x y := by ext aA; simp
  map_smul' z x := by ext aA; simp

def pairFiber {n : ℕ} (A : Finset (Fin n)) : PairStackSpace n →ₗ[ℂ] PairSpace n where
  toFun z := WithLp.toLp 2 (fun a => z (a, A))
  map_add' _x _y := rfl
  map_smul' _z _x := rfl

theorem pairStack_norm_sq {n : ℕ} (x : Space n) :
    ‖pairStack x‖ ^ 2 = ∑ a : PairIndex n, ‖pairMode a x‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  exact (EuclideanSpace.norm_sq_eq (pairMode a x)).symm

theorem pairStack_norm_on_sector {n N : ℕ} {x : Space n} (hx : InSector N x) :
    ‖pairStack x‖ = Real.sqrt (N.choose 2 : ℝ) * ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [pairStack_norm_sq, sum_pairMode_norm_sq hx, mul_pow,
    Real.sq_sqrt (Nat.cast_nonneg _)]

theorem pairStackSpace_norm_sq {n : ℕ} (z : PairStackSpace n) :
    ‖z‖ ^ 2 = ∑ A : Finset (Fin n), ‖pairFiber A z‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, Finset.sum_comm]
  simp only [EuclideanSpace.norm_sq_eq]
  rfl

/-- Q acts on pair indices, leaving the remaining occupation label unchanged.
This is the concrete finite Hilbert tensor amplification, in l2 coordinates. -/
def pairAmplify {n : ℕ} (Q : Module.End ℂ (PairSpace n)) :
    Module.End ℂ (PairStackSpace n) where
  toFun z := WithLp.toLp 2 (fun aA => Q (pairFiber aA.2 z) aA.1)
  map_add' x y := by ext aA; simp
  map_smul' z x := by ext aA; simp

theorem pairAmplify_fiber {n : ℕ} (Q : Module.End ℂ (PairSpace n))
    (z : PairStackSpace n) (A : Finset (Fin n)) :
    pairFiber A (pairAmplify Q z) = Q (pairFiber A z) := rfl

theorem pairAmplify_norm_le {n : ℕ} (Q : Module.End ℂ (PairSpace n))
    (z : PairStackSpace n) :
    ‖pairAmplify Q z‖ ≤ ‖LinearMap.toContinuousLinearMap Q‖ * ‖z‖ := by
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [pairStackSpace_norm_sq, mul_pow, pairStackSpace_norm_sq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro A _
  rw [pairAmplify_fiber, ← mul_pow]
  exact (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
    ((LinearMap.toContinuousLinearMap Q).le_opNorm (pairFiber A z))

theorem pairMatrix_apply {n : ℕ} (Q : Module.End ℂ (PairSpace n))
    (p : PairSpace n) (a : PairIndex n) :
    Q p a = ∑ b : PairIndex n, p b * Q (pairBasis b) a := by
  have h : Q p = ∑ b : PairIndex n, p b • Q (pairBasis b) := by
    simp_rw [← map_smul]
    rw [← map_sum, pairBasis_expansion]
  rw [h]
  simp

theorem pairStack_amplify_inner {n : ℕ} (Q : Module.End ℂ (PairSpace n))
    (x y : Space n) :
    inner ℂ (pairStack x) (pairAmplify Q (pairStack y)) =
      ∑ a : PairIndex n, ∑ b : PairIndex n,
        Q (pairBasis b) a * inner ℂ (pairMode a x) (pairMode b y) := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type]
  simp only [RCLike.inner_apply]
  change (∑ a, ∑ A, Q (pairFiber A (pairStack y)) a * conj (pairMode a x A)) = _
  conv_lhs =>
    arg 2; ext a
    arg 2; ext A
    rw [pairMatrix_apply]
  change (∑ a, ∑ A, (∑ b, pairMode b y A * Q (pairBasis b) a) *
    conj (pairMode a x A)) = _
  simp_rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [PiLp.inner_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A _
  simp only [RCLike.inner_apply]
  ring

theorem pairLift_gram {n : ℕ} (Q : Module.End ℂ (PairSpace n)) (x y : Space n) :
    inner ℂ x (pairLift Q y) = inner ℂ (pairStack x) (pairAmplify Q (pairStack y)) := by
  rw [pairStack_amplify_inner]
  simp only [pairLift, pairCreate, LinearMap.sum_apply, Module.End.mul_apply,
    LinearMap.smul_apply, inner_sum, inner_smul_right, LinearMap.adjoint_inner_right]
  rw [Finset.sum_comm]

/-- Factorization of the previously defined matrix lift, valid for every Q on full Fock space. -/
theorem pairLift_factorization {n : ℕ} (Q : Module.End ℂ (PairSpace n)) :
    pairLift Q = pairStack.adjoint ∘ₗ pairAmplify Q ∘ₗ pairStack := by
  apply LinearMap.ext
  intro y
  apply ext_inner_left ℂ
  intro x
  change inner ℂ x (pairLift Q y) =
    inner ℂ x (pairStack.adjoint (pairAmplify Q (pairStack y)))
  rw [pairLift_gram, LinearMap.adjoint_inner_right]

/-- Uniform in the mode count, for every (not necessarily self-adjoint) pair operator Q. -/
theorem pairLift_norm_le_on_sector {n N : ℕ} (Q : Module.End ℂ (PairSpace n))
    {x : Space n} (hx : InSector N x) :
    ‖pairLift Q x‖ ≤ (N.choose 2 : ℝ) * ‖LinearMap.toContinuousLinearMap Q‖ * ‖x‖ := by
  have h : ‖pairLift Q x‖ ^ 2 ≤ ‖pairLift Q x‖ *
      ((N.choose 2 : ℝ) * ‖LinearMap.toContinuousLinearMap Q‖ * ‖x‖) := by
    calc
      _ = (inner ℂ (pairLift Q x) (pairLift Q x)).re :=
        norm_sq_eq_re_inner (𝕜 := ℂ) (pairLift Q x)
      _ = (inner ℂ (pairStack (pairLift Q x)) (pairAmplify Q (pairStack x))).re :=
        congrArg Complex.re (pairLift_gram Q (pairLift Q x) x)
      _ ≤ ‖pairStack (pairLift Q x)‖ * ‖pairAmplify Q (pairStack x)‖ :=
        re_inner_le_norm (𝕜 := ℂ) _ _
      _ ≤ ‖pairStack (pairLift Q x)‖ *
          (‖LinearMap.toContinuousLinearMap Q‖ * ‖pairStack x‖) :=
        mul_le_mul_of_nonneg_left (pairAmplify_norm_le Q (pairStack x)) (norm_nonneg _)
      _ = _ := by
        rw [pairStack_norm_on_sector (pairLift_preserves_sector Q hx),
          pairStack_norm_on_sector hx]
        calc
          _ = ‖pairLift Q x‖ * (Real.sqrt (N.choose 2 : ℝ) ^ 2 *
              ‖LinearMap.toContinuousLinearMap Q‖ * ‖x‖) := by ring
          _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg _)]
  by_cases hzero : ‖pairLift Q x‖ = 0
  · rw [hzero]
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)) (norm_nonneg _)
  · rw [pow_two] at h
    exact le_of_mul_le_mul_left h (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero))

/-- The full occupation N-sector as an actual Hilbert subspace. -/
def particleSector (n N : ℕ) : Submodule ℂ (Space n) where
  carrier := {x | InSector N x}
  zero_mem' := sector_zero
  add_mem' := fun hx hy => sector_add hx hy
  smul_mem' := fun z _ hx => sector_smul z hx

def pairLiftSector {n : ℕ} (N : ℕ) (Q : Module.End ℂ (PairSpace n)) :
    particleSector n N →L[ℂ] particleSector n N :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => ⟨pairLift Q x, pairLift_preserves_sector Q x.property⟩
      map_add' := fun x y => Subtype.ext (map_add (pairLift Q) (x : Space n) (y : Space n))
      map_smul' := fun z x => Subtype.ext (map_smul (pairLift Q) z (x : Space n)) }

theorem pairLiftSector_apply {n N : ℕ} (Q : Module.End ℂ (PairSpace n))
    (x : particleSector n N) :
    (pairLiftSector N Q x : Space n) = pairLift Q (x : Space n) := rfl

/-- The norm here is the induced Hilbert operator norm on the full N-particle sector. -/
theorem pairLiftSector_opNorm_le {n N : ℕ} (Q : Module.End ℂ (PairSpace n)) :
    ‖pairLiftSector N Q‖ ≤ (N.choose 2 : ℝ) * ‖LinearMap.toContinuousLinearMap Q‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
  intro x
  exact pairLift_norm_le_on_sector Q x.property

theorem pairAnnihilate_basis {n : ℕ} (a : PairIndex n) :
    pairAnnihilate (pairBasis a) = pairMode a := by
  unfold pairAnnihilate
  rw [Finset.sum_eq_single a]
  · simp [pairBasis]
  · intro b _ hba
    simp [pairBasis, hba]
  · simp

theorem pairCreate_basis {n : ℕ} (a : PairIndex n) :
    pairCreate (pairBasis a) = (pairMode a).adjoint := by
  rw [← pairAnnihilate_adjoint, pairAnnihilate_basis]

/-- Off-diagonal rank-one operators as well as positive pair projectors. -/
theorem pairLift_outer {n : ℕ} (p q : PairSpace n) :
    pairLift (InnerProductSpace.rankOne ℂ p q).toLinearMap =
      pairCreate p * pairAnnihilate q := by
  have h (b : PairIndex n) : (InnerProductSpace.rankOne ℂ p q).toLinearMap (pairBasis b) =
      conj (q b) • p := by
    change (inner ℂ q (PiLp.single 2 b 1)) • p = _
    rw [EuclideanSpace.inner_single_right]
    simp
  simp only [pairLift, h, pairCreate_smul, smul_mul_assoc,
    pairAnnihilate, Finset.mul_sum, mul_smul_comm]

end VortexGap.Fermion
