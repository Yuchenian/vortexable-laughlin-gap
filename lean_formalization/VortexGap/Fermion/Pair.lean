import VortexGap.Fermion.Finite

/-! Ordered, unit-normalized pairs in the full occupation Fock representation. -/
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped BigOperators InnerProduct ComplexConjugate
open OAI.LaughlinGap.Occupation

abbrev PairIndex (n : ℕ) := {ij : Fin n × Fin n // ij.1 < ij.2}
abbrev PairSpace (n : ℕ) := EuclideanSpace ℂ (PairIndex n)

def pairMode {n : ℕ} (a : PairIndex n) : Module.End ℂ (Space n) :=
  annihilateMode a.val.2 * annihilateMode a.val.1

def pairKet {n : ℕ} (a : PairIndex n) : Space n :=
  pairMode a |>.adjoint <| ket ∅

theorem pairMode_vacuum {n : ℕ} (a : PairIndex n) : pairMode a (ket ∅) = 0 := by
  simp [pairMode, Module.End.mul_apply, annihilate_vacuum]

theorem pairMode_adjoint {n : ℕ} (a : PairIndex n) :
    (pairMode a).adjoint = createMode a.val.1 * createMode a.val.2 := by
  simp [pairMode, adjoint_mul]

theorem pairMode_pairKet {n : ℕ} (a b : PairIndex n) :
    pairMode a (pairKet b) = if a = b then ket ∅ else 0 := by
  have hcross : ¬(a.val.2 = b.val.1 ∧ a.val.1 = b.val.2) := by
    rintro ⟨h₁, h₂⟩
    have ha := a.property
    have hb := b.property
    rw [h₁, h₂] at ha
    exact (lt_asymm ha hb)
  have heq : (a.val.1 = b.val.1 ∧ a.val.2 = b.val.2) ↔ a = b := by
    constructor
    · rintro ⟨h₁, h₂⟩; exact Subtype.ext (Prod.ext h₁ h₂)
    · intro h; subst b; exact ⟨rfl, rfl⟩
  change (pairMode a * (pairMode b).adjoint) (ket ∅) = _
  rw [pairMode_adjoint]
  simp only [pairMode, ← mul_assoc]
  rw [pair_normal_order]
  simp only [hcross, heq, ite_false, LinearMap.add_apply, LinearMap.sub_apply,
    sub_zero, Module.End.mul_apply,
    show ∀ i : Fin n, annihilation i (ket ∅) = 0 from annihilate_vacuum, map_zero, add_zero]
  split_ifs <;> simp [Module.End.mul_apply,
    show ∀ i : Fin n, annihilation i (ket ∅) = 0 from annihilate_vacuum]

theorem pairKet_inner {n : ℕ} (a b : PairIndex n) :
    inner ℂ (pairKet a) (pairKet b) = if a = b then 1 else 0 := by
  change inner ℂ ((pairMode a).adjoint (ket ∅)) (pairKet b) = _
  rw [LinearMap.adjoint_inner_left, pairMode_pairKet]
  split_ifs <;> simp [inner_self_eq_norm_sq_to_K, ket_norm]

theorem pairKet_norm {n : ℕ} (a : PairIndex n) : ‖pairKet a‖ = 1 := by
  have hr : ‖pairKet a‖ ^ 2 = (1 : ℝ) := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), pairKet_inner]
    simp
  nlinarith [norm_nonneg (pairKet a)]

def pairEmbed {n : ℕ} : PairSpace n →ₗ[ℂ] Space n where
  toFun p := ∑ a, p a • pairKet a
  map_add' p q := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' z p := by simp [Finset.smul_sum, smul_smul]

def pairAnnihilate {n : ℕ} (p : PairSpace n) : Module.End ℂ (Space n) :=
  ∑ a, conj (p a) • pairMode a

theorem pairMode_pairEmbed {n : ℕ} (a : PairIndex n) (p : PairSpace n) :
    pairMode a (pairEmbed p) = p a • ket ∅ := by
  simp [pairEmbed, map_sum, pairMode_pairKet]

theorem pairAnnihilate_pairEmbed {n : ℕ} (p q : PairSpace n) :
    pairAnnihilate p (pairEmbed q) = (inner ℂ p q) • ket ∅ := by
  simp only [pairAnnihilate, LinearMap.sum_apply, LinearMap.smul_apply,
    pairMode_pairEmbed, smul_smul, ← Finset.sum_smul]
  congr 1
  simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]

theorem pairAnnihilate_vacuum {n : ℕ} (p : PairSpace n) :
    pairAnnihilate p (ket ∅) = 0 := by
  simp [pairAnnihilate, LinearMap.sum_apply, pairMode_vacuum]

theorem pairEmbed_inner {n : ℕ} (p q : PairSpace n) :
    inner ℂ (pairEmbed p) (pairEmbed q) = inner ℂ p q := by
  change inner ℂ (∑ a, p a • pairKet a) (∑ b, q b • pairKet b) = _
  simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right, pairKet_inner]
  simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]

theorem pairEmbed_norm {n : ℕ} (p : PairSpace n) : ‖pairEmbed p‖ = ‖p‖ :=
  (LinearMap.norm_map_iff_inner_map_map (pairEmbed (n := n))).mpr pairEmbed_inner p

def pairEmbedding (n : ℕ) : PairSpace n →ₗᵢ[ℂ] Space n where
  toLinearMap := pairEmbed
  norm_map' := pairEmbed_norm

theorem mode_create_vacuum {n : ℕ} (i k : Fin n) :
    annihilateMode i (createMode k (ket ∅)) = if i = k then ket ∅ else 0 := by
  change (annihilation i * creation k) (ket ∅) = _
  rw [annihilation_creation]
  split_ifs <;> simp [Module.End.mul_apply,
    show annihilation i (ket ∅) = 0 from annihilate_vacuum i]

theorem pairMode_oneParticle {n : ℕ} (a : PairIndex n) (k : Fin n) :
    pairMode a (createMode k (ket ∅)) = 0 := by
  simp only [pairMode, Module.End.mul_apply, mode_create_vacuum]
  split_ifs <;> simp [annihilate_vacuum]

theorem pairAnnihilate_oneParticle {n : ℕ} (p : PairSpace n)
    (v : EuclideanSpace ℂ (Fin n)) : pairAnnihilate p (create v (ket ∅)) = 0 := by
  simp [pairAnnihilate, create, LinearMap.sum_apply, map_sum, pairMode_oneParticle]

def pairCreate {n : ℕ} (p : PairSpace n) : Module.End ℂ (Space n) :=
  ∑ a, p a • (pairMode a).adjoint

theorem pairAnnihilate_adjoint {n : ℕ} (p : PairSpace n) :
    (pairAnnihilate p).adjoint = pairCreate p := by
  simp [pairAnnihilate, pairCreate, map_sum, map_smulₛₗ]

theorem pairCreate_vacuum {n : ℕ} (p : PairSpace n) :
    pairCreate p (ket ∅) = pairEmbed p := by
  simp [pairCreate, pairEmbed, pairKet, LinearMap.sum_apply]

theorem pairCreate_smul {n : ℕ} (z : ℂ) (p : PairSpace n) :
    pairCreate (z • p) = z • pairCreate p := by
  simp [pairCreate, Finset.smul_sum, smul_smul]

theorem pairAnnihilate_smul {n : ℕ} (z : ℂ) (p : PairSpace n) :
    pairAnnihilate (z • p) = conj z • pairAnnihilate p := by
  simp [pairAnnihilate, Finset.smul_sum, smul_smul]

def pairBasis {n : ℕ} (a : PairIndex n) : PairSpace n := PiLp.single 2 a 1

theorem pairBasis_expansion {n : ℕ} (p : PairSpace n) :
    ∑ a, p a • pairBasis a = p := by
  ext a
  simp [pairBasis, Pi.single_apply]

/-- The matrix second-quantization of a two-particle operator. Each unordered
pair occurs once. Positivity is not built into the definition. -/
def pairLift {n : ℕ} (Q : Module.End ℂ (PairSpace n)) : Module.End ℂ (Space n) :=
  ∑ b, pairCreate (Q (pairBasis b)) * pairMode b

theorem pairLift_pairEmbed {n : ℕ} (Q : Module.End ℂ (PairSpace n)) (p : PairSpace n) :
    pairLift Q (pairEmbed p) = pairEmbed (Q p) := by
  simp only [pairLift, LinearMap.sum_apply, Module.End.mul_apply, pairMode_pairEmbed,
    map_smul, pairCreate_vacuum]
  simp_rw [← map_smul]
  rw [← map_sum, ← map_sum, pairBasis_expansion]

theorem pairLift_vacuum {n : ℕ} (Q : Module.End ℂ (PairSpace n)) :
    pairLift Q (ket ∅) = 0 := by
  simp [pairLift, LinearMap.sum_apply, Module.End.mul_apply, pairMode_vacuum]

theorem pairLift_oneParticle {n : ℕ} (Q : Module.End ℂ (PairSpace n))
    (v : EuclideanSpace ℂ (Fin n)) : pairLift Q (create v (ket ∅)) = 0 := by
  simp [pairLift, create, LinearMap.sum_apply, Module.End.mul_apply, map_sum,
    pairMode_oneParticle]

def pairRankOne {n : ℕ} (p : PairSpace n) : Module.End ℂ (PairSpace n) :=
  (InnerProductSpace.rankOne ℂ p p).toLinearMap

theorem pairLift_rankOne {n : ℕ} (p : PairSpace n) :
    pairLift (pairRankOne p) = (pairAnnihilate p).adjoint * pairAnnihilate p := by
  have h (b : PairIndex n) : pairRankOne p (pairBasis b) = conj (p b) • p := by
    change (inner ℂ p (PiLp.single 2 b 1)) • p = _
    rw [EuclideanSpace.inner_single_right]
    simp
  rw [pairAnnihilate_adjoint]
  simp only [pairLift, h, pairCreate_smul, smul_mul_assoc,
    pairAnnihilate, Finset.mul_sum, mul_smul_comm]

theorem pairCreate_add {n : ℕ} (p q : PairSpace n) :
    pairCreate (p + q) = pairCreate p + pairCreate q := by
  simp [pairCreate, add_smul, Finset.sum_add_distrib]

theorem pairLift_add {n : ℕ} (Q R : Module.End ℂ (PairSpace n)) :
    pairLift (Q + R) = pairLift Q + pairLift R := by
  simp [pairLift, pairCreate_add, add_mul, Finset.sum_add_distrib]

theorem pairLift_smul {n : ℕ} (z : ℂ) (Q : Module.End ℂ (PairSpace n)) :
    pairLift (z • Q) = z • pairLift Q := by
  simp [pairLift, pairCreate_smul, Finset.smul_sum]

theorem pairLift_zero {n : ℕ} : pairLift (0 : Module.End ℂ (PairSpace n)) = 0 := by
  simp [pairLift, pairCreate]

def pairLiftLinear (n : ℕ) : Module.End ℂ (PairSpace n) →ₗ[ℂ] Module.End ℂ (Space n) where
  toFun := pairLift
  map_add' := pairLift_add
  map_smul' := pairLift_smul

/-- Exact finite-frame identity; weights have not been absorbed twice. -/
theorem pairLift_frame {n : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (p : ι → PairSpace n) :
    pairLift (∑ x, (w x : ℂ) • pairRankOne (p x)) =
      ∑ x, (w x : ℂ) • ((pairAnnihilate (p x)).adjoint * pairAnnihilate (p x)) := by
  change pairLiftLinear n (∑ x, (w x : ℂ) • pairRankOne (p x)) = _
  rw [map_sum]
  simp only [map_smul]
  exact Finset.sum_congr rfl fun x _ => congrArg ((w x : ℂ) • ·) (pairLift_rankOne (p x))

/-- Positivity of the matrix lift is derived from the finite-dimensional
spectral decomposition, not included in its definition. -/
theorem pairLift_positive {n : ℕ} (Q : Module.End ℂ (PairSpace n)) (hQ : Q.IsPositive) :
    (pairLift Q).IsPositive := by
  have hQc : (LinearMap.toContinuousLinearMap Q).IsPositive :=
    Q.isPositive_toContinuousLinearMap_iff.mpr hQ
  obtain ⟨m, u, hu⟩ := ContinuousLinearMap.isPositive_iff_eq_sum_rankOne.mp hQc
  have he : Q = ∑ i : Fin m, pairRankOne (u i) := by
    simpa [pairRankOne] using
      congrArg ContinuousLinearMap.toLinearMap hu
  rw [he]
  change (pairLiftLinear n (∑ i : Fin m, pairRankOne (u i))).IsPositive
  rw [map_sum]
  apply LinearMap.isPositive_sum
  intro i _
  change (pairLift (pairRankOne (u i))).IsPositive
  rw [pairLift_rankOne]
  exact LinearMap.isPositive_adjoint_comp_self _

theorem pairLift_positive_difference {n : ℕ} (Q R : Module.End ℂ (PairSpace n))
    (hQR : (R - Q).IsPositive) : (pairLift R - pairLift Q).IsPositive := by
  change (pairLiftLinear n R - pairLiftLinear n Q).IsPositive
  rw [← map_sub]
  exact pairLift_positive (R - Q) hQR

end VortexGap.Fermion
