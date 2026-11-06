import VortexGap.Frame.TwoNoiseFactorization

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped BigOperators InnerProduct ComplexConjugate

abbrev OrbitalStackSpace (n : ℕ) := FrameStackSpace (Fin n) n

/-- One orbital and a system Fock state, in ordinary l2 product coordinates. -/
def orbitalProduct {n : ℕ} : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] Space n →ₗ[ℂ] OrbitalStackSpace n where
  toFun u := {
    toFun x := WithLp.toLp 2 (fun iA => u iA.1 * x iA.2)
    map_add' x y := by ext iA; simp [mul_add]
    map_smul' z x := by ext iA; simp [mul_left_comm] }
  map_add' u v := by ext x iA; simp [add_mul]
  map_smul' z u := by ext x iA; simp [mul_assoc]

theorem orbitalProduct_apply {n : ℕ} (u : EuclideanSpace ℂ (Fin n)) (x : Space n)
    (i : Fin n) (A : Finset (Fin n)) : orbitalProduct u x (i,A) = u i * x A := rfl

theorem orbitalProduct_inner {n : ℕ} (u v : EuclideanSpace ℂ (Fin n)) (x y : Space n) :
    inner ℂ (orbitalProduct u x) (orbitalProduct v y) = inner ℂ u v * inner ℂ x y := by
  simp only [PiLp.inner_apply, Fintype.sum_prod_type, orbitalProduct_apply,
    RCLike.inner_apply, map_mul, Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun A _ => by ring

theorem orbitalProduct_fiber {n : ℕ} (u : EuclideanSpace ℂ (Fin n)) (x : Space n)
    (A : Finset (Fin n)) : frameFiber A (orbitalProduct u x) = x A • u := by
  ext i
  simp only [frameFiber_apply, orbitalProduct_apply, PiLp.smul_apply, smul_eq_mul, mul_comm]

/-- The actual one-particle state created from the environment vacuum. -/
def singleParticleEmbed {n : ℕ} : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] Space n where
  toFun u := create u (ket ∅)
  map_add' u v := by rw [create_add, LinearMap.add_apply]
  map_smul' z u := by rw [create_smul, LinearMap.smul_apply]; rfl

theorem singleParticleEmbed_apply {n : ℕ} (u : EuclideanSpace ℂ (Fin n)) :
    singleParticleEmbed u = create u (ket ∅) := rfl

theorem singleParticleEmbed_inner {n : ℕ} (u v : EuclideanSpace ℂ (Fin n)) :
    inner ℂ (singleParticleEmbed u) (singleParticleEmbed v) = inner ℂ u v := by
  rw [singleParticleEmbed_apply, singleParticleEmbed_apply, ← annihilate_adjoint u,
    LinearMap.adjoint_inner_left, vector_create_vacuum]
  simp [inner_smul_right, inner_self_eq_norm_sq_to_K, ket_norm]

theorem singleParticleEmbed_norm {n : ℕ} (u : EuclideanSpace ℂ (Fin n)) :
    ‖singleParticleEmbed u‖ = ‖u‖ :=
  (LinearMap.norm_map_iff_inner_map_map (singleParticleEmbed (n := n))).mpr singleParticleEmbed_inner u

def orbitalEnvironmentEmbed {n : ℕ} : OrbitalStackSpace n →ₗ[ℂ] SplitSpace n n where
  toFun z := WithLp.toLp 2 (fun AB => singleParticleEmbed (frameFiber AB.2 z) AB.1)
  map_add' x y := by ext AB; simp
  map_smul' z x := by ext AB; simp

theorem orbitalEnvironmentEmbed_apply {n : ℕ} (z : OrbitalStackSpace n)
    (A B : Finset (Fin n)) :
    orbitalEnvironmentEmbed z (A,B) = singleParticleEmbed (frameFiber B z) A := rfl

theorem orbitalEnvironmentEmbed_norm_sq {n : ℕ} (z : OrbitalStackSpace n) :
    ‖orbitalEnvironmentEmbed z‖^2 = ‖z‖^2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, Finset.sum_comm, frameStack_norm_sq]
  apply Finset.sum_congr rfl
  intro B _
  calc
    _ = ‖singleParticleEmbed (frameFiber B z)‖^2 := (EuclideanSpace.norm_sq_eq _).symm
    _ = _ := by rw [singleParticleEmbed_norm]

theorem orbitalEnvironmentEmbed_product {n : ℕ} (u : EuclideanSpace ℂ (Fin n)) (x : Space n) :
    orbitalEnvironmentEmbed (orbitalProduct u x) = fockProduct (create u (ket ∅)) x := by
  ext ⟨A,B⟩
  simp only [orbitalEnvironmentEmbed_apply, orbitalProduct_fiber, map_smul,
    PiLp.smul_apply, smul_eq_mul, singleParticleEmbed_apply, fockProduct_apply, mul_comm]

/-- The one-particle operator acts on the orbital index and preserves the system occupation. -/
def orbitalAmplify {n : ℕ}
    (T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :
    Module.End ℂ (OrbitalStackSpace n) where
  toFun z := WithLp.toLp 2 (fun iA => T (frameFiber iA.2 z) iA.1)
  map_add' x y := by ext iA; simp
  map_smul' z x := by ext iA; simp

theorem orbitalAmplify_fiber {n : ℕ}
    (T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (z : OrbitalStackSpace n) (A : Finset (Fin n)) :
    frameFiber A (orbitalAmplify T z) = T (frameFiber A z) := rfl

theorem orbitalAmplify_norm_le {n : ℕ}
    (T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) (z : OrbitalStackSpace n) :
    ‖orbitalAmplify T z‖ ≤ ‖T‖ * ‖z‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [frameStack_norm_sq, mul_pow, frameStack_norm_sq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro A _
  rw [orbitalAmplify_fiber, ← mul_pow]
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr (T.le_opNorm _)

theorem orbitalAmplify_product {n : ℕ}
    (T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (u : EuclideanSpace ℂ (Fin n)) (x : Space n) :
    orbitalAmplify T (orbitalProduct u x) = orbitalProduct (T u) x := by
  ext ⟨i,A⟩
  change T (frameFiber A (orbitalProduct u x)) i = T u i * x A
  rw [orbitalProduct_fiber, map_smul]
  simp only [PiLp.smul_apply, smul_eq_mul, mul_comm]

end VortexGap.Fermion
