import VortexGap.Fermion.PairCompatibility

/-! Concrete first-index contraction and all-N CAR covariance.
All maps use actual occupation sectors; annihilation lowers and creation raises
the sector. No upper particle-number truncation or dilation hypothesis is used. -/
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped BigOperators InnerProduct ComplexConjugate
open OAI.LaughlinGap.Occupation

theorem tensorPure_basis {n N : ℕ} (b : Fin N → Fin n) :
    tensorPure (fun i => (PiLp.single 2 (b i) (1 : ℂ) : EuclideanSpace ℂ (Fin n))) =
      PiLp.single 2 b 1 := by
  classical
  ext a
  change tensorKernel (LinearMap.id : Module.End ℂ (EuclideanSpace ℂ (Fin n))) a b = _
  rw [tensorKernel_id]
  simp [PiLp.single_apply, eq_comm]

theorem tensorPure_expansion {n N : ℕ} (ψ : TensorSpace n N) :
    (∑ b : Fin N → Fin n, ψ b • tensorPure
      (fun i => (PiLp.single 2 (b i) (1 : ℂ) : EuclideanSpace ℂ (Fin n)))) = ψ := by
  simp only [tensorPure_basis]
  ext a
  simp [Pi.single_apply]

/-- Contraction of the first tensor index, antilinear in the orbital v. -/
def tensorContract {n N : ℕ} (v : EuclideanSpace ℂ (Fin n)) :
    TensorSpace n (N + 1) →ₗ[ℂ] TensorSpace n N where
  toFun ψ := WithLp.toLp 2 (fun a => ∑ i, conj (v i) * ψ (Fin.cons i a))
  map_add' ψ φ := by ext a; simp only [PiLp.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' z ψ := by
    ext a
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => mul_left_comm _ _ _

theorem tensorContract_apply {n N : ℕ} (v : EuclideanSpace ℂ (Fin n))
    (ψ : TensorSpace n (N + 1)) (a : Fin N → Fin n) :
    tensorContract v ψ a = ∑ i, conj (v i) * ψ (Fin.cons i a) := rfl

theorem tensorContract_pure {n N : ℕ} (v : EuclideanSpace ℂ (Fin n))
    (w : Fin (N + 1) → EuclideanSpace ℂ (Fin n)) :
    tensorContract v (tensorPure w) = (inner ℂ v (w 0)) • tensorPure (fun i => w i.succ) := by
  ext a
  change (∑ i : Fin n, conj (v i) * (∏ j, w j ((Fin.cons i a : Fin (N+1) → Fin n) j))) =
    inner ℂ v (w 0) * (∏ j, w j.succ (a j))
  simp_rw [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, ← mul_assoc]
  rw [← Finset.sum_mul]
  congr 1
  simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]

theorem tensorContract_tensorPower {n m N : ℕ}
    (A : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m))
    (v : EuclideanSpace ℂ (Fin m)) (ψ : TensorSpace n (N + 1)) :
    tensorContract v (tensorPower A (N + 1) ψ) =
      tensorPower A N (tensorContract (A.adjoint v) ψ) := by
  have hp (w : Fin (N + 1) → EuclideanSpace ℂ (Fin n)) :
      tensorContract v (tensorPower A (N + 1) (tensorPure w)) =
        tensorPower A N (tensorContract (A.adjoint v) (tensorPure w)) := by
    rw [tensorPower_pure, tensorContract_pure, tensorContract_pure, map_smul, tensorPower_pure,
      LinearMap.adjoint_inner_left]
  conv_lhs => rw [← tensorPure_expansion ψ]
  conv_rhs => rw [← tensorPure_expansion ψ]
  simp only [map_sum, map_smul, hp]

def sectorRawReadout (n N : ℕ) : particleSector n N →ₗ[ℂ] TensorSpace n N :=
  (rawReadout n N).comp (particleSector n N).subtype

theorem sectorRawReadout_injective (n N : ℕ) : Function.Injective (sectorRawReadout n N) := by
  intro x y h
  apply (sectorTensorIsometry n N).injective
  apply Subtype.ext
  change ((Real.sqrt (N.factorial : ℝ))⁻¹ : ℂ) • sectorRawReadout n N x =
    ((Real.sqrt (N.factorial : ℝ))⁻¹ : ℂ) • sectorRawReadout n N y
  rw [h]

theorem exteriorPower_rawReadout {n m : ℕ}
    (A : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m)) (N : ℕ)
    (x : particleSector n N) :
    sectorRawReadout m N (exteriorPower A N x) = tensorPower A N (sectorRawReadout n N x) := by
  have h := congrArg Subtype.val (exteriorPower_tensor A N x)
  change normalizedReadout m N (exteriorPower A N x : Space m) =
    tensorPower A N (normalizedReadout n N (x : Space n)) at h
  simp only [normalizedReadout, LinearMap.smul_apply, map_smul] at h
  have hc : ((Real.sqrt (N.factorial : ℝ))⁻¹ : ℂ) ≠ 0 := by
    exact_mod_cast inv_ne_zero (ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast Nat.factorial_pos N)))
  exact smul_right_injective (TensorSpace m N) hc h

theorem annihilate_sector {n N : ℕ} (v : EuclideanSpace ℂ (Fin n))
    {x : Space n} (hx : InSector (N + 1) x) : InSector N (annihilate v x) := by
  simp only [annihilate, LinearMap.sum_apply, LinearMap.smul_apply]
  exact sector_sum _ _ fun i _ => sector_smul _ (annihilateMode_sector i hx)

theorem create_sector {n N : ℕ} (v : EuclideanSpace ℂ (Fin n))
    {x : Space n} (hx : InSector N x) : InSector (N + 1) (create v x) := by
  simp only [create, LinearMap.sum_apply, LinearMap.smul_apply]
  exact sector_sum _ _ fun i _ => sector_smul _ (createMode_sector i hx)

def annihilateSector {n : ℕ} (N : ℕ) (v : EuclideanSpace ℂ (Fin n)) :
    particleSector n (N + 1) →ₗ[ℂ] particleSector n N where
  toFun x := ⟨annihilate v x, annihilate_sector v x.property⟩
  map_add' x y := Subtype.ext (map_add (annihilate v) (x : Space n) (y : Space n))
  map_smul' z x := Subtype.ext (map_smul (annihilate v) z (x : Space n))

def createSector {n : ℕ} (N : ℕ) (v : EuclideanSpace ℂ (Fin n)) :
    particleSector n N →ₗ[ℂ] particleSector n (N + 1) where
  toFun x := ⟨create v x, create_sector v x.property⟩
  map_add' x y := Subtype.ext (map_add (create v) (x : Space n) (y : Space n))
  map_smul' z x := Subtype.ext (map_smul (create v) z (x : Space n))

theorem rawReadout_annihilate {n N : ℕ} (v : EuclideanSpace ℂ (Fin n)) (x : Space n) :
    rawReadout n N (annihilate v x) = tensorContract v (rawReadout n (N + 1) x) := by
  ext a
  simp only [tensorContract_apply, rawReadout_succ, Fin.cons_zero, Fin.cons_succ,
    annihilate, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
    WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul]

theorem sectorRawReadout_annihilate {n N : ℕ} (v : EuclideanSpace ℂ (Fin n))
    (x : particleSector n (N + 1)) :
    sectorRawReadout n N (annihilateSector N v x) =
      tensorContract v (sectorRawReadout n (N + 1) x) := rawReadout_annihilate v x

/-- Exact CAR contraction intertwining for arbitrary A, including singular maps. -/
theorem exteriorPower_annihilate {n m N : ℕ}
    (A : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m))
    (v : EuclideanSpace ℂ (Fin m)) (x : particleSector n (N + 1)) :
    annihilateSector N v (exteriorPower A (N + 1) x) =
      exteriorPower A N (annihilateSector N (A.adjoint v) x) := by
  apply sectorRawReadout_injective m N
  rw [sectorRawReadout_annihilate, exteriorPower_rawReadout, tensorContract_tensorPower,
    exteriorPower_rawReadout, sectorRawReadout_annihilate]

theorem annihilateSector_adjoint {n : ℕ} (N : ℕ) (v : EuclideanSpace ℂ (Fin n)) :
    LinearMap.adjoint (𝕜 := ℂ) (E := particleSector n (N+1)) (F := particleSector n N)
      (annihilateSector N v) = createSector N v := by
  symm
  apply (LinearMap.eq_adjoint_iff (𝕜 := ℂ) (E := particleSector n N)
    (F := particleSector n (N+1)) (createSector N v) (annihilateSector N v)).mpr
  intro x y
  change inner ℂ (create v (x : Space n)) (y : Space n) =
    inner ℂ (x : Space n) (annihilate v (y : Space n))
  rw [← annihilate_adjoint, LinearMap.adjoint_inner_left]

theorem antisymmetricPower_adjoint {n m : ℕ}
    (A : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m)) (N : ℕ) :
    antisymmetricPower A.adjoint N =
      LinearMap.adjoint (𝕜 := ℂ) (E := antisymmetricTensors n N) (F := antisymmetricTensors m N)
        (antisymmetricPower A N) := by
  apply (LinearMap.eq_adjoint_iff (𝕜 := ℂ) (E := antisymmetricTensors m N)
    (F := antisymmetricTensors n N) (antisymmetricPower A.adjoint N)
    (antisymmetricPower A N)).mpr
  intro x y
  change inner ℂ (tensorPower A.adjoint N (x : TensorSpace m N)) (y : TensorSpace n N) =
    inner ℂ (x : TensorSpace m N) (tensorPower A N (y : TensorSpace n N))
  rw [tensorPower_adjoint, LinearMap.adjoint_inner_left]

theorem exteriorPower_adjoint {n m : ℕ}
    (A : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m)) (N : ℕ) :
    exteriorPower A.adjoint N =
      LinearMap.adjoint (𝕜 := ℂ) (E := particleSector n N) (F := particleSector m N)
        (exteriorPower A N) := by
  have hn := LinearIsometryEquiv.adjoint_toLinearMap_eq_symm (𝕜 := ℂ)
    (H := particleSector n N) (K := antisymmetricTensors n N) (sectorTensorIsometry n N)
  have hm := LinearIsometryEquiv.adjoint_toLinearMap_eq_symm (𝕜 := ℂ)
    (H := antisymmetricTensors m N) (K := particleSector m N) (sectorTensorIsometry m N).symm
  unfold exteriorPower
  rw [LinearMap.adjoint_comp (𝕜 := ℂ) (E := particleSector n N)
    (F := antisymmetricTensors m N) (G := particleSector m N)]
  rw [LinearMap.adjoint_comp (𝕜 := ℂ) (E := particleSector n N)
    (F := antisymmetricTensors n N) (G := antisymmetricTensors m N)]
  rw [hn, hm, ← antisymmetricPower_adjoint]
  rfl

theorem exteriorPower_annihilate_map {n m : ℕ}
    (A : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m)) (N : ℕ)
    (v : EuclideanSpace ℂ (Fin m)) :
    (annihilateSector N v).comp (exteriorPower A (N + 1)) =
      (exteriorPower A N).comp (annihilateSector N (A.adjoint v)) := by
  apply LinearMap.ext
  exact exteriorPower_annihilate A v

theorem exteriorPower_create_map {n m : ℕ}
    (A : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m)) (N : ℕ)
    (v : EuclideanSpace ℂ (Fin n)) :
    (exteriorPower A (N + 1)).comp (createSector N v) =
      (createSector N (A v)).comp (exteriorPower A N) := by
  have h := congrArg (LinearMap.adjoint (𝕜 := ℂ)
    (E := particleSector m (N+1)) (F := particleSector n N))
    (exteriorPower_annihilate_map A.adjoint N v)
  rw [LinearMap.adjoint_comp (𝕜 := ℂ) (E := particleSector m (N+1))
    (F := particleSector n (N+1)) (G := particleSector n N)] at h
  rw [LinearMap.adjoint_comp (𝕜 := ℂ) (E := particleSector m (N+1))
    (F := particleSector m N) (G := particleSector n N)] at h
  simpa only [← exteriorPower_adjoint,
    LinearMap.adjoint_adjoint, annihilateSector_adjoint] using h

theorem exteriorPower_create {n m N : ℕ}
    (A : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m))
    (v : EuclideanSpace ℂ (Fin n)) (x : particleSector n N) :
    exteriorPower A (N + 1) (createSector N v x) =
      createSector N (A v) (exteriorPower A N x) :=
  congrArg (fun T => T x) (exteriorPower_create_map A N v)

end VortexGap.Fermion
