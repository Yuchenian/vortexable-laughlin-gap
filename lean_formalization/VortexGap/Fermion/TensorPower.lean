import VortexGap.Fermion.TensorSector

/-! Concrete finite Hilbert tensor powers of arbitrary one-particle maps.
Matrix coefficients, adjoints, isometries and permutation covariance are derived. -/
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped BigOperators InnerProduct ComplexConjugate

private theorem euclidean_expansion {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : EuclideanSpace ℂ ι) : (∑ i, x i • PiLp.single 2 i (1 : ℂ)) = x := by
  ext i
  simp [Pi.single_apply]

theorem orbital_map_apply {n m : ℕ}
    (A : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m))
    (x : EuclideanSpace ℂ (Fin n)) (i : Fin m) :
    A x i = ∑ j, A (PiLp.single 2 j 1) i * x j := by
  conv_lhs => rw [← euclidean_expansion x]
  simp only [map_sum, map_smul, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

def tensorKernel {n m N : ℕ}
    (A : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m))
    (a : Fin N → Fin m) (b : Fin N → Fin n) : ℂ :=
  ∏ i, A (PiLp.single 2 (b i) 1) (a i)

def tensorPower {n m : ℕ}
    (A : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m)) (N : ℕ) :
    TensorSpace n N →ₗ[ℂ] TensorSpace m N where
  toFun ψ := WithLp.toLp 2 (fun a => ∑ b, tensorKernel A a b * ψ b)
  map_add' ψ φ := by
    ext a
    simp only [PiLp.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' z ψ := by
    ext a
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => mul_left_comm _ _ _

theorem tensorPower_apply {n m N : ℕ}
    (A : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m))
    (ψ : TensorSpace n N) (a : Fin N → Fin m) :
    tensorPower A N ψ a = ∑ b, tensorKernel A a b * ψ b := rfl

theorem tensorPower_basis {n m N : ℕ}
    (A : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m))
    (b : Fin N → Fin n) (a : Fin N → Fin m) :
    tensorPower A N (PiLp.single 2 b 1) a = tensorKernel A a b := by
  classical
  simp [tensorPower_apply, PiLp.single_apply]

theorem tensorKernel_comp {n m l N : ℕ}
    (A : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m))
    (B : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] EuclideanSpace ℂ (Fin l))
    (a : Fin N → Fin l) (b : Fin N → Fin n) :
    tensorKernel (B.comp A) a b =
      ∑ c : Fin N → Fin m, tensorKernel B a c * tensorKernel A c b := by
  calc
    _ = ∏ i, ∑ j, B (PiLp.single 2 j 1) (a i) * A (PiLp.single 2 (b i) 1) j := by
      exact Finset.prod_congr rfl fun i _ => orbital_map_apply B _ _
    _ = ∑ c : Fin N → Fin m, ∏ i,
        B (PiLp.single 2 (c i) 1) (a i) * A (PiLp.single 2 (b i) 1) (c i) :=
      Fintype.prod_sum _
    _ = _ := by simp only [tensorKernel, Finset.prod_mul_distrib]

theorem tensorPower_comp {n m l : ℕ}
    (A : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m))
    (B : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] EuclideanSpace ℂ (Fin l)) (N : ℕ) :
    tensorPower (B.comp A) N = (tensorPower B N).comp (tensorPower A N) := by
  ext ψ a
  simp only [LinearMap.comp_apply, tensorPower_apply, tensorKernel_comp,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  exact Finset.sum_congr rfl fun b _ => mul_assoc _ _ _

theorem tensorKernel_id {n N : ℕ} (a b : Fin N → Fin n) :
    tensorKernel (LinearMap.id : Module.End ℂ (EuclideanSpace ℂ (Fin n))) a b =
      if a = b then 1 else 0 := by
  classical
  by_cases hab : a = b
  · subst b
    simp [tensorKernel]
  · rw [ite_eq_right_iff.mpr (fun h => (hab h).elim)]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hab
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

theorem tensorPower_id (n N : ℕ) :
    tensorPower (LinearMap.id : Module.End ℂ (EuclideanSpace ℂ (Fin n))) N =
      LinearMap.id := by
  classical
  ext ψ a
  simp [tensorPower_apply, tensorKernel_id]

private theorem orbital_adjoint_apply {n m : ℕ}
    (A : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m))
    (i : Fin n) (j : Fin m) :
    A.adjoint (PiLp.single 2 j 1) i = conj (A (PiLp.single 2 i 1) j) := by
  have h := LinearMap.adjoint_inner_right A (PiLp.single 2 i 1) (PiLp.single 2 j 1)
  simpa only [EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right,
    map_one, one_mul] using h

theorem tensorKernel_adjoint {n m N : ℕ}
    (A : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m))
    (a : Fin N → Fin n) (b : Fin N → Fin m) :
    tensorKernel A.adjoint a b = conj (tensorKernel A b a) := by
  simp only [tensorKernel, orbital_adjoint_apply, map_prod]

theorem tensorPower_adjoint {n m : ℕ}
    (A : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m)) (N : ℕ) :
    tensorPower A.adjoint N = (tensorPower A N).adjoint := by
  apply (LinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  have hb (a : Fin N → Fin m) (b : Fin N → Fin n) :
      inner ℂ (tensorPower A.adjoint N (PiLp.single 2 a 1)) (PiLp.single 2 b 1) =
        inner ℂ (PiLp.single 2 a 1) (tensorPower A N (PiLp.single 2 b 1)) := by
    simp only [EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right,
      map_one, one_mul, tensorPower_basis, tensorKernel_adjoint]
    simp
  rw [← euclidean_expansion x, ← euclidean_expansion y]
  simp only [map_sum, map_smul, sum_inner, inner_sum, inner_smul_left, inner_smul_right, hb]

theorem tensorPower_isometry_inner {n m : ℕ}
    (U : EuclideanSpace ℂ (Fin n) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m)) (N : ℕ)
    (x y : TensorSpace n N) :
    inner ℂ (tensorPower U.toLinearMap N x) (tensorPower U.toLinearMap N y) = inner ℂ x y := by
  have hu : U.toLinearMap.adjoint.comp U.toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    intro v
    apply ext_inner_left ℂ
    intro w
    change inner ℂ w (U.toLinearMap.adjoint (U v)) = inner ℂ w v
    rw [LinearMap.adjoint_inner_right]
    exact U.inner_map_map w v
  rw [← LinearMap.adjoint_inner_right]
  rw [← tensorPower_adjoint]
  change inner ℂ x (((tensorPower U.toLinearMap.adjoint N).comp
    (tensorPower U.toLinearMap N)) y) = _
  rw [← tensorPower_comp, hu, tensorPower_id, LinearMap.id_apply]

def tensorPowerIsometry {n m : ℕ}
    (U : EuclideanSpace ℂ (Fin n) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m)) (N : ℕ) :
    TensorSpace n N →ₗᵢ[ℂ] TensorSpace m N where
  toLinearMap := tensorPower U.toLinearMap N
  norm_map' := (LinearMap.norm_map_iff_inner_map_map _).mpr
    (tensorPower_isometry_inner U N)

def configurationPerm {n N : ℕ} (σ : Equiv.Perm (Fin N)) :
    (Fin N → Fin n) ≃ (Fin N → Fin n) where
  toFun a := a ∘ σ
  invFun a := a ∘ σ.symm
  left_inv a := by funext i; simp
  right_inv a := by funext i; simp

def tensorPerm {n N : ℕ} (σ : Equiv.Perm (Fin N)) : Module.End ℂ (TensorSpace n N) where
  toFun ψ := WithLp.toLp 2 (fun a => ψ (a ∘ σ))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem tensorKernel_perm {n m N : ℕ}
    (A : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m))
    (σ : Equiv.Perm (Fin N)) (a : Fin N → Fin m) (b : Fin N → Fin n) :
    tensorKernel A (a ∘ σ) (b ∘ σ) = tensorKernel A a b := by
  exact Equiv.prod_comp σ (fun i => A (PiLp.single 2 (b i) 1) (a i))

theorem tensorPower_perm {n m N : ℕ}
    (A : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m))
    (σ : Equiv.Perm (Fin N)) (ψ : TensorSpace n N) :
    tensorPerm σ (tensorPower A N ψ) = tensorPower A N (tensorPerm σ ψ) := by
  ext a
  change (∑ b, tensorKernel A (a ∘ σ) b * ψ b) =
    ∑ b, tensorKernel A a b * ψ (b ∘ σ)
  calc
    _ = ∑ b, tensorKernel A (a ∘ σ) (b ∘ σ) * ψ (b ∘ σ) :=
      ((configurationPerm σ).sum_comp (fun b => tensorKernel A (a ∘ σ) b * ψ b)).symm
    _ = _ := Finset.sum_congr rfl fun b _ => by rw [tensorKernel_perm]

theorem tensorPower_preserves_antisymmetric {n m N : ℕ}
    (A : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m))
    {ψ : TensorSpace n N} (hψ : ψ ∈ antisymmetricTensors n N) :
    tensorPower A N ψ ∈ antisymmetricTensors m N := by
  intro i j hij a
  have hs : tensorPerm (Equiv.swap i j) ψ = -ψ := by
    ext b
    exact hψ i j hij b
  have hp := congrArg (fun φ : TensorSpace m N => φ a)
    (tensorPower_perm A (Equiv.swap i j) ψ)
  rw [hs, map_neg] at hp
  exact hp

end VortexGap.Fermion
